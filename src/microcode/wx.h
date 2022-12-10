#ifndef SCHEME_WX_H
#define SCHEME_WX_H

#include <stddef.h>
#include <stdint.h>

void * cons_xccblock (const void *, size_t);
void mark_xccblock (void *, void **);
struct xccblock * pop_xccblock_rw (void **, void **);
void commit_xccblock_rx (struct xccblock *);
void sweep_xccblocks (void);

#endif /* SCHEME_WX_H */
