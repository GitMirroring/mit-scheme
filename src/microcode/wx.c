#include "wx.h"

#include <sys/mman.h>

#include <stddef.h>

#include "dstack.h"
#include "object.h"
#include "os.h"
#include "prims.h"
#include "syscall.h"

#include "wb.c"

#define container_of(P, T, M) ((T *) (((char *) (P)) - (offsetof (T, M))))

void block_signals (void); /* XXX */
void preserve_signal_mask (void); /* XXX */

/* struct xccblock: Metadata about an executable compiled code block.

   - Contains a pointer to the actual mmapped region which is
     mprotected read/write to initialize and during garbage collection,
     and mprotected read/execute at all other times.

   - Arranged in a tree so we can do O(log n) lookups to identify the
     struct xccblock metadata given a pointer into the block, such as a
     compiled code entry, during garbage collection.

   - Also arranged in a list of live blocks, during garbage collection,
     so that the garbage collector can trace each live block to
     relocate any pointers into the heap.

   - Tagged with an epoch number, mod 2.  During garbage collection,
     marking a block advances it to the next epoch.  At the end of
     garbage collection, only blocks in the next epoch are dead; all
     others can be swept away.  */

struct xccblock
{
  uintptr_t ptr;
  size_t nbytes;
  struct wb node;
  struct xccblock * next;
  bool epoch;
};

static bool xcc_epoch;		/* current epoch number */
static struct wb * xcc_root;	/* root of xccblock tree for ptr lookup */

/* xcc_nodecmp(cookie, na, nb): -1 if na precedes nb, +1 if na follows
   nb, 0 if they overlap.  */

static int
xcc_nodecmp(void * cookie, const struct wb * na, const struct wb * nb)
{
  const struct xccblock * Xa = (container_of (na, struct xccblock, node));
  const struct xccblock * Xb = (container_of (nb, struct xccblock, node));

  if (((Xa->ptr) + (Xa->nbytes)) < (Xb->ptr))
    return (-1);
  if ((Xa->ptr) > ((Xb->ptr) + (Xb->nbytes)))
    return (+1);
  return (0);
}

/* xcc_keycmp(cookie, key, node): -1 if key precedes node, +1 if key
   follows node, 0 if key points somewhere inside node.  */

static int
xcc_keycmp(void * cookie, const void * key, const struct wb * node)
{
  const uintptr_t ptr = ((uintptr_t) key);
  const struct xccblock * X = (container_of (node, struct xccblock, node));

  if (ptr < (X->ptr))
    return (-1);
  if (ptr >= ((X->ptr) + (X->nbytes)))
    return (+1);
  return (0);
}

/* struct cons_xccblock: State during allocation in cons_xccblock, so
   that we can unwind mmap on failure.  */

struct cons_xccblock
{
  void * p;
  size_t nbytes;
};

/* cons_xccblock_abort (cookie): Called if cons_xccblock fails or is
   interrupted to unwind the cons.  cookie is a pointer to a struct
   cons_xccblock object.  */

static void
cons_xccblock_abort (void * cookie)
{
  struct cons_xccblock * C = cookie;

  if ((C->p) != MAP_FAILED)
    (void) munmap ((C->p), (C->nbytes));
}

/* cons_xccblock (data, nbytes): Mmap a region to store nbytes from
   data but mapped read/execute.  Returns a pointer to the read/execute
   memory.  Stores metadata in a static tree.  */

void *
cons_xccblock (const void * data, size_t nbytes)
{
  const int prot = (PROT_READ | PROT_EXEC);
  const int initprot = (PROT_READ | PROT_WRITE | (PROT_MPROTECT (prot)));
  const int flags = (MAP_ANONYMOUS | MAP_PRIVATE);
  struct cons_xccblock cons = { .p = MAP_FAILED, .nbytes = nbytes };
  struct cons_xccblock * C = (&cons);
  struct xccblock * X;
  struct wb * node UNUSED;

  transaction_begin ();

  preserve_signal_mask ();
  block_signals ();

  transaction_record_action (tat_abort, cons_xccblock_abort, C);

  (C->p) = (mmap (NULL, nbytes, initprot, flags, -1, 0));
  if ((C->p) == MAP_FAILED)
    error_system_call (errno, syscall_mmap);
  if (((uintptr_t) (C->p)) & TYPE_CODE_MASK)
    error_external_return ();
  memcpy ((C->p), data, nbytes);
  if ((mprotect ((C->p), nbytes, prot)) == -1)
    error_system_call (errno, syscall_mprotect);

  X = (OS_malloc (sizeof (*X)));
  (X->ptr) = ((uintptr_t) (C->p));
  (X->nbytes) = nbytes;
  (X->epoch) = xcc_epoch;
  node = (wb_insert_key_compare3 ((&xcc_root), (&X->node), xcc_nodecmp, NULL));
  assert (node == (&X->node));

  transaction_commit ();

  return (C->p);
}

/* mark_xccblock (ptr, queue): ptr must point somewhere inside a block
   returned by cons_xccblock.  Marks it live, and if it was not
   previously marked live, queues it up for later use with
   pop_xccblock_rw.  */

void
mark_xccblock (void * ptr, void ** queue)
{
  struct xccblock * X;
  struct wb * node;

  node = (wb_find_key_compare3 (xcc_root, ptr, xcc_keycmp, NULL));
  assert (node != NULL);
  X = (container_of (node, struct xccblock, node));
  if ((X->epoch) != xcc_epoch)
    return;
  (X->epoch) = (!xcc_epoch);
  (X->next) = (*queue);
  (*queue) = X;
}

/* pop_xccblock_rw(queue, &ptr): If queue is nonempty, removes a block
   previously queued by mark_xccblock, sets ptr to its pointer, and
   returns a pointer to the struct xccblock metadata for subsequent use
   by commit_xccblock_rx.  During the time between pop_xccblock_rw and
   commit_xccblock_rx, the block is mapped read/write, not
   read/execute.  Caller is expected to trace, and possibly relocate,
   pointers inside the block.  */

struct xccblock *
pop_xccblock_rw (void ** queue, void ** ptrp)
{
  struct xccblock * X = (*queue);

  (*queue) = (X->next);
  if ((mprotect (((void *) (X->ptr)), (X->nbytes), (PROT_READ | PROT_WRITE)))
      == -1)
    error_system_call (errno, syscall_mprotect); /* XXX fatal */
  (*ptrp) = ((void *) (X->ptr));
  return (X);
}

/* commit_xccblock_rx(xccblock): Called when caller has finished
   tracing and relocating pointers in xccblock obtained by
   pop_xccblock_rw.  */

void
commit_xccblock_rx (struct xccblock * X)
{
  if ((mprotect (((void *) (X->ptr)), (X->nbytes), (PROT_READ | PROT_EXEC)))
      == -1)
    error_system_call (errno, syscall_mprotect); /* XXX fatal */
}

/* sweep_xccblocks(): Called after caller has marked and finished
   tracing all xccblocks in the heap.  Frees the unmarked ones and
   resets the mark epoch for the next GC.  */

void
sweep_xccblocks (void)
{
  struct wb * node;
  struct wb * next;
  struct xccblock * X;

  xcc_epoch = (!xcc_epoch);
  for (node = (wb_first (xcc_root)); node != NULL; node = next)
    {
      next = (wb_next (node));
      X = (container_of (node, struct xccblock, node));
      if ((X->epoch) == xcc_epoch) /* marked */
	continue;
      wb_delete ((&xcc_root), (&X->node));
      (void) munmap (((void *) (X->ptr)), (X->nbytes));
      OS_free (X);
    }
}
