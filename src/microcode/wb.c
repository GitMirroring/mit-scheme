/*
 * wb: Weight-balanced trees.
 *
 *	Weight-balanced trees are standard binary trees where each node
 *	annotated with the number of nodes, including itself, in the
 *	subtree rooted at that node, called its size.  The size is used
 *	for balancing and for indexing.
 */

/*-
 * Copyright (c) 2015 Taylor R. Campbell
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <assert.h>
#include <limits.h>

#define	wb_assert	assert

#include "wb.h"

/*
 * weight
 *
 *	Map a size to a weight.
 */
static inline size_t
weight(size_t s)
{

	return s;
}

/*
 * log2_lt
 *
 *	True if floor(log_2 a) < floor(log_2 b), treating log_2 0 as
 *	-1.
 */
static inline bool
log2_lt(size_t a, size_t b)
{

	return (a < b) && (((a & b) << 1) < b);
}

/*
 * unbalanced_weight
 *
 *	True if sw (`smaller weight') is too much smaller than bw
 *	(`bigger weight').  True result implies sw < bw.
 */
static inline bool
unbalanced_weight(size_t sw, size_t bw)
{

	return log2_lt(sw, bw >> 1);
}

/*
 * single_rotation
 *
 *	True if iw (`interior weight') is not so much larger than ew
 *	(`exterior weight') that a double rotation is required.
 */
static inline bool
single_rotation(size_t iw, size_t ew)
{

	return !log2_lt(ew, iw);
}

/*
 * The size and direction in the parent are represented by a single
 * size_t quantity.  Since nodes are represented by at least four
 * distinct bytes, we assume we have at least log_2 4 = 2 bits at the
 * most significant end of a size_t that will always be zero.  We use
 * one such bit to encode the node's direction in its parent.  For the
 * root node, the direction is always zero.
 */
#define	NODE_DIR_SHIFT	((CHAR_BIT * sizeof(size_t)) - 1)
#define	NODE_SIZE_MASK	(((size_t)1 << NODE_DIR_SHIFT) - 1)

/*
 * node_size
 *
 *	Number of nodes rooted at node.  Zero if node is null, positive
 *	otherwise.
 */
static inline size_t
node_size(struct wb *node)
{

	return node == NULL ? 0 : (node->wb_size_dir & NODE_SIZE_MASK);
}

/*
 * node_weight
 *
 *	Weight of node for balancing purposes.
 */
static inline size_t
node_weight(struct wb *node)
{

	return weight(node_size(node));
}

/*
 * node_dir
 *
 *	Index of node in its parent's children, or zero if node is a
 *	root.
 */
static inline unsigned
node_dir(struct wb *node)
{

	return node->wb_size_dir >> NODE_DIR_SHIFT;
}

/*
 * node_ptr
 *
 *	Pointer to the dir child of parent, or rootp if parent is NULL.
 */
static inline struct wb **
node_ptr(struct wb **rootp, struct wb *parent, unsigned dir)
{

	wb_assert(parent != NULL || dir == 0);
	return parent == NULL ? rootp : &parent->wb_child[dir];
}

/*
 * unbalanced_child
 *
 *	True if the child of node in the direction dir is too much
 *	larger than the child in the other direction.
 */
static inline bool
unbalanced_child(struct wb *node, unsigned dir)
{
	size_t sw, bw;

	wb_assert(node != NULL);
	sw = node_weight(node->wb_child[1^dir]);
	bw = node_weight(node->wb_child[dir]);
	return unbalanced_weight(sw, bw);
}

/*
 * nearbalanced_child
 *
 *	True if the child of node in the direction dir is at most too
 *	much larger by 1 than the child in the other direction -- in
 *	other words, if the node would be rebalanced by a rotation.
 */
static inline bool
nearbalanced_child(struct wb *node, unsigned dir)
{
	size_t sw, bw;

	wb_assert(node != NULL);
	if (node->wb_child[dir] == NULL)
		return true;
	wb_assert(0 < node_size(node->wb_child[dir]));
	sw = weight(node_size(node->wb_child[1^dir]) + 1);
	bw = weight(node_size(node->wb_child[dir]) - 1);
	return !unbalanced_weight(sw, bw);
}

/*
 * node_valid_p
 *
 *	True if the node's size is nonzero.
 */
static inline bool
node_valid_p(struct wb *node)
{

	return (node->wb_size_dir & NODE_SIZE_MASK) != 0;
}

/*
 * invalidate
 *
 *	Mark node invalid by setting its size to zero.
 */
static inline void
invalidate(struct wb *node)
{

	wb_assert(node_valid_p(node));
	node->wb_size_dir &= ~NODE_SIZE_MASK;
}

/*
 * revalidate
 *
 *	Calculate the size of node, which must be invalid, and store it
 *	in node->wb_size.
 */
static inline void
revalidate(struct wb *node)
{

	wb_assert(!node_valid_p(node));
	node->wb_size_dir |=
	    node_size(node->wb_child[0])
	    + 1
	    + node_size(node->wb_child[1]);
	wb_assert(!unbalanced_child(node, 0));
	wb_assert(!unbalanced_child(node, 1));
}

/*
 * check
 *
 *	Asssert that node is valid and its children are balanced.
 */
static inline void
check(struct wb *node)
{

	(void)node;
	wb_assert(node == NULL || node_valid_p(node));
	wb_assert(node == NULL ||
	    (node_size(node) ==
		node_size(node->wb_child[0])
		+ 1
		+ node_size(node->wb_child[1])));
	wb_assert(node == NULL || !unbalanced_child(node, 0));
	wb_assert(node == NULL || !unbalanced_child(node, 1));
}

/*
 * node_init
 *
 *	Initialize a node as a detached but valid singleton.
 */
static inline void
node_init(struct wb *node)
{

	wb_assert(node != NULL);
	node->wb_child[0] = NULL;
	node->wb_child[1] = NULL;
	node->wb_parent = NULL;
	node->wb_size_dir = 1;
}

/*
 * node_fini
 *
 *	Clear a node that has been invalidated and detached.
 */
static inline void
node_fini(struct wb *node)
{

	(void)node;
	wb_assert(node != NULL);
	wb_assert(node->wb_child[0] == NULL);
	wb_assert(node->wb_child[1] == NULL);
	wb_assert(node->wb_parent == NULL);
	wb_assert(!node_valid_p(node));
}

/*
 * attach
 *
 *	Attach node as child of parent in the direction dir, storing
 *	node in *nodep, which must hold NULL.  If parent is nonnull,
 *	i.e. node is not being made the root, then nodep must be
 *	&parent->wb_child[dir].
 *
 *	Afterward, the ancestors may have the wrong sizes and may be
 *	unbalanced; caller is responsible for fixing this.
 */
static inline void
attach(struct wb *parent, unsigned dir, struct wb *node,
    struct wb **nodep)
{

	wb_assert(parent != NULL || dir == 0);
	wb_assert(nodep != NULL);
	wb_assert(*nodep == NULL);
	wb_assert(parent == NULL || nodep == &parent->wb_child[dir]);
	wb_assert(node != NULL);
	wb_assert(node->wb_parent == NULL);
	wb_assert(node_dir(node) == 0);

	*nodep = node;
	node->wb_parent = parent;
	node->wb_size_dir |= (size_t)dir << NODE_DIR_SHIFT;
}

/*
 * detach
 *
 *	Detach node as child of parent in the direction dir, storing
 *	NULL in *nodep, which must hold node.  If parent is nonnull,
 *	i.e. node is not the root, the nodep must be
 *	&parent->wb_child[dir].
 */
static inline void
detach(struct wb *parent, unsigned dir, struct wb *node,
    struct wb **nodep)
{

	(void)parent;
	(void)dir;
	wb_assert(parent != NULL || dir == 0);
	wb_assert(nodep != NULL);
	wb_assert(*nodep == node);
	wb_assert(parent == NULL || nodep == &parent->wb_child[dir]);
	wb_assert(node != NULL);
	wb_assert(node->wb_parent == parent);
	wb_assert(node_dir(node) == dir);

	*nodep = NULL;
	node->wb_parent = NULL;
	node->wb_size_dir &= NODE_SIZE_MASK;
}

/*
 * rotate
 *
 *	The child of *np in the direction dir is too heavy.  Rotate it
 *	back to fix the balance of this subtree, storing the new root
 *	of the subtree back in *np.
 */
static void
rotate(struct wb **np, unsigned dir)
{
	struct wb *p, *n, *nb;
	struct wb *nbe, *nbi;
	unsigned pdir;

	n = *np;
	wb_assert(n != NULL);
	p = n->wb_parent;			/* parent */
	pdir = node_dir(n);			/* parent direction */
	nb = n->wb_child[dir];			/* bigger child */
	wb_assert(nb != NULL);
	nbe = nb->wb_child[dir];		/* exterior grandchild */
	nbi = nb->wb_child[dir ^ 1];		/* interior grandchild */

	wb_assert(unbalanced_child(n, dir));
	wb_assert(nearbalanced_child(n, dir));
	if (single_rotation(node_weight(nbi), node_weight(nbe))) {
		/*
		 *          n                           nb
		 *         / \                         /  \
		 *       ns   nb         ===>         n   nbe
		 *           /  \                    / \
		 *         nbi  nbe                 ns  nbi
		 */

		/* Invalidate n and nb since their children change.  */
		invalidate(n);
		invalidate(nb);

		/* Detach n, nb, and nbi.  */
		detach(p, pdir, n,	np);
		detach(n, dir, nb,	&n->wb_child[dir]);
		if (nbi != NULL)
			detach(nb, 1^dir, nbi, &nb->wb_child[1^dir]);

		/* Reattach n, nb, and nbi.  */
		attach(p, pdir, nb,	np);
		attach(nb, 1^dir, n,	&nb->wb_child[1^dir]);
		if (nbi != NULL)
			attach(n, dir, nbi, &n->wb_child[dir]);

		/* Restore sizes, children first.  */
		revalidate(n);
		revalidate(nb);

		/* Check all the nodes we touched.  */
		check(n);
		check(nb);
		if (nbi != NULL)
			check(nbi);
	} else {
		/*
		 *          n
		 *         / \                          nbi
		 *       ns   nb                      /     \
		 *           /  \        ===>        n       nb
		 *         nbi  nbe                 / \     /  \
		 *        /  \                    ns nbii nbie nbe
		 *     nbii  nbie
		 */
		struct wb *nbii, *nbie;

		wb_assert(nbi != NULL);
		nbii = nbi->wb_child[1^dir];
		nbie = nbi->wb_child[dir];

		/* Invalidate n, nb, and nbi since their children change.  */
		invalidate(n);
		invalidate(nb);
		invalidate(nbi);

		/* Detach n, nb, nbi, nbii, and nbie.  */
		detach(p, pdir, n,	np);
		detach(n, dir, nb,	&n->wb_child[dir]);
		detach(nb, 1^dir, nbi,	&nb->wb_child[1^dir]);
		if (nbii != NULL)
			detach(nbi, 1^dir, nbii, &nbi->wb_child[1^dir]);
		if (nbie != NULL)
			detach(nbi, dir, nbie, &nbi->wb_child[dir]);

		/* Reattach n, nb, nbi, nbii, and nbie.  */
		attach(p, pdir, nbi,	np);
		attach(nbi, 1^dir, n,	&nbi->wb_child[1^dir]);
		if (nbii != NULL)
			attach(n, dir, nbii,	&n->wb_child[dir]);
		attach(nbi, dir, nb,	&nbi->wb_child[dir]);
		if (nbie != NULL)
			attach(nb, 1^dir, nbie,	&nb->wb_child[1^dir]);

		/* Restore sizes, children first.  */
		revalidate(n);
		revalidate(nb);
		revalidate(nbi);

		/* Check all the nodes we touched.  */
		check(n);
		check(nb);
		check(nbi);
		if (nbie != NULL)
			check(nbie);
		if (nbii != NULL)
			check(nbii);
	}
}

/*
 * insert
 *
 *	Initialize node and insert it as child of parent in the
 *	direction dir in the tree rooted at *rootp, update ancestors to
 *	increase their sizes by one, and rebalance the tree.  The
 *	parent must not already have such a child, or, if the parent is
 *	null, the tree must be empty.
 */
static void
insert(struct wb **rootp, struct wb *parent, unsigned dir, struct wb *node)
{
	struct wb *p, *pp;
	unsigned pdir;

	wb_assert(rootp != NULL);
	wb_assert(node != NULL);
	wb_assert(parent == NULL || parent->wb_child[dir] == NULL);
	wb_assert(parent != NULL || *rootp == NULL);

	/* Initialize the node as a singleton and attach it to the parent.  */
	node_init(node);
	attach(parent, dir, node, node_ptr(rootp, parent, dir));

	/*
	 * Adjust the tree from the bottom up to the root:
	 * - Increment each ancestor's size.
	 * - Rotate if necessary.
	 */
	for (p = parent; p != NULL; p = pp, dir = pdir) {
		pp = p->wb_parent;
		pdir = node_dir(p);
		p->wb_size_dir++;
		wb_assert(nearbalanced_child(p, dir));
		if (unbalanced_child(p, dir))
			rotate(node_ptr(rootp, pp, pdir), dir);
	}
}

/*
 * delete_extreme
 *
 *	Detach the extreme node in the subtree rooted at node in the
 *	direction dir and return it.  The result may be node itself.
 */
static struct wb *
delete_extreme(struct wb *node, unsigned dir)
{
	struct wb *subroot, *pp, *p, *n, *c;
	unsigned pdir;

	wb_assert(node != NULL);
	wb_assert(node->wb_parent != NULL);
	subroot = node->wb_parent;

	/* Find the extreme node and invalidate it.  */
	for (n = node; (c = n->wb_child[dir]) != NULL; n = c)
		continue;
	invalidate(n);

	/* Detach its other child, if any.  */
	if ((c = n->wb_child[1^dir]) != NULL)
		detach(n, 1^dir, c, &n->wb_child[1^dir]);

	/* Find its parent.  */
	p = n->wb_parent;
	wb_assert(p != NULL);

	/* Detach from the parent and rebalance.  */
	if (n == node) {
		/*
		 * If the extreme node is node, it may be either of its
		 * parent's children.  Just detach it.  No rebalancing
		 * needed: the caller will handle sizing and balancing
		 * beyond the parent.  But this node is guaranteed not
		 * to be the root, so we need not use node_ptr.
		 *
		 * Can't check p because it is invalid already -- it is
		 * being deleted.
		 */
		wb_assert(!node_valid_p(p));
		dir = node_dir(node);
		detach(p, dir, node, &p->wb_child[dir]);
		if (c != NULL)
			attach(p, dir, c, &p->wb_child[dir]);
	} else {
		/*
		 * Otherwise, the extreme node is below.  Detach it,
		 * and adjust the subtree from the bottom up to node:
		 * - Decrement each ancestor's size.
		 * - Rotate if necessary.
		 */
		detach(p, dir, n, &p->wb_child[dir]);
		if (c != NULL)
			attach(p, dir, c, &p->wb_child[dir]);
		for (; p != subroot; p = pp, dir = pdir) {
			pp = p->wb_parent;
			wb_assert(pp != NULL);
			pdir = node_dir(p);
			wb_assert(0 < node_size(p));
			p->wb_size_dir--;
			wb_assert(nearbalanced_child(p, 1^dir));
			if (unbalanced_child(p, 1^dir))
				rotate(&pp->wb_child[pdir], 1^dir);
			check(p);
		}
	}
	assert(n->wb_child[dir] == NULL);
	assert(n->wb_child[1^dir] == NULL);

	return n;
}

/*
 * delete
 *
 *	Delete node from the tree rooted at *rootp, update ancestors to
 *	decrease their sizes by one, and rebalance the tree.  The node
 *	must be in the tree already.
 */
static void
delete(struct wb **rootp, struct wb *node)
{
	struct wb *p = node->wb_parent;
	struct wb *pp;
	unsigned dir = node_dir(node);
	unsigned pdir;
	struct wb **nodep = node_ptr(rootp, p, dir);
	struct wb *c0 = node->wb_child[0];
	struct wb *c1 = node->wb_child[1];

	wb_assert(*nodep == node);
	wb_assert(node_valid_p(node));

	/* Invalidate the node so it can't be used internally more.  */
	invalidate(node);

	/* Detach it.  */
	detach(p, dir, node, nodep);

	/* Migrate the children.  */
	if (c0 == NULL && c1 == NULL) {
		/* No children: nothing to do.  */
	} else {
		/*
		 * Detach the extreme node of whichever child's subtree
		 * is larger, and replace node by it.
		 *
		 *	n                      m
		 *     / \                    / \
		 *    d   c        ===>      d   c
		 *       / \                    / \
		 *      m   y                  x   y
		 *       \
		 *        x
		 */
		unsigned cdir;
		struct wb *c, *m, *d;

		/* Pick the larger of the children, preferring 0.  */
		cdir = (node_size(c0) < node_size(c1) ? 1 : 0);
		c = node->wb_child[cdir];
		wb_assert(c != NULL);

		/*
		 * Detach the extreme node in the direction opposite
		 * that of the child chosen, i.e. the next one after
		 * node.  We will replace node by it.
		 */
		m = delete_extreme(c, 1^cdir);
		wb_assert(!node_valid_p(m));
		wb_assert(m->wb_child[cdir] == NULL);
		wb_assert(m->wb_child[1^cdir] == NULL);

		/*
		 * If there is still a child on this side, i.e. m was
		 * not it, then move it from node to m.  Note that
		 * detaching m may have caused rotations moving the
		 * root of the subtree at node->wb_child[cdir], so we
		 * must reload c.
		 */
		c = node->wb_child[cdir];
		check(c);
		if (c != NULL) {
			wb_assert(c != m);
			detach(node, cdir, c, &node->wb_child[cdir]);
			attach(m, cdir, c, &m->wb_child[cdir]);
		}

		/* Move node's other child to m too.  */
		d = node->wb_child[1^cdir];
		if (d != NULL) {
			detach(node, 1^cdir, d, &node->wb_child[1^cdir]);
			attach(m, 1^cdir, d, &m->wb_child[1^cdir]);
		}

		/* m is all set up.  */
		revalidate(m);
		check(m);
		check(d);
		check(c);

		/* Attach m in the place of node.  */
		attach(p, dir, m, nodep);
	}

	/*
	 * Adjust the tree from the bottom up to the root:
	 * - Decrement each ancestor's size.
	 * - Rotate if necessary.
	 */
	for (; p != NULL; p = pp, dir = pdir) {
		pp = p->wb_parent;
		pdir = node_dir(p);
		wb_assert(0 < node_size(p));
		p->wb_size_dir--;
		wb_assert(nearbalanced_child(p, 1^dir));
		if (unbalanced_child(p, 1^dir))
			rotate(node_ptr(rootp, pp, pdir), 1^dir);
	}

	node_fini(node);
}

/*
 * wb_size
 *
 *	Number of nodes in the subtree rooted at node.
 */
size_t
wb_size(struct wb *node)
{

	return node_size(node);
}

/*
 * wb_iter_start
 *
 *	Return the first node in the direction dir, or NULL if the tree
 *	is empty.
 */
struct wb *
wb_iter_start(struct wb *node, unsigned dir)
{
	struct wb *n, *c;

	/* If the subtree is empty, return NULL.  */
	if (node == NULL)
		return NULL;

	/*
	 * Otherwise, find the last node in the chain of links in the
	 * direction opposite dir before NULL.
	 */
	for (n = node; (c = n->wb_child[1^dir]) != NULL; n = c)
		continue;

	return n;
}

/*
 * wb_first
 *
 *	Return the leftmost node in the subtree rooted at node, or NULL
 *	if the subtree is empty.
 */
struct wb *
wb_first(struct wb *node)
{

	return wb_iter_start(node, 1);
}


/*
 * wb_last
 *
 *	Return the rightmost node in the subtree rooted at node, or
 *	NULL if the subtree is empty.
 */
struct wb *
wb_last(struct wb *node)
{

	return wb_iter_start(node, 0);
}

/*
 * wb_iter
 *
 *	Return the next node after node in the direction dir, or NULL
 *	if there are no more in the tree.
 */
struct wb *
wb_iter(struct wb *node, unsigned dir)
{
	struct wb *p, *n, *c;

	wb_assert(node != NULL);
	wb_assert(dir == (dir & 1));

	/*
	 * If there is a child in that direction, choose the extreme
	 * descendant of that child in the opposite direction.
	 */
	c = node->wb_child[dir];
	if (c != NULL) {
		for (n = c; (c = n->wb_child[1^dir]) != NULL; n = c)
			continue;
		return n;
	}

	/*
	 * Otherwise, walk up in the opposite direction as far as we
	 * can, and return the first parent in that direction.
	 */
	for (n = node; (p = n->wb_parent) != NULL; n = p) {
		/* node_dir(n) != dir */
		if ((node_dir(n) ^ dir) != 0)
			break;
	}

	return p;
}

/*
 * wb_next
 *
 *	Return the next node, or NULL if there are no more.
 */
struct wb *
wb_next(struct wb *node)
{

	return wb_iter(node, 1);
}

/*
 * wb_prev
 *
 *	Return the previous node, or NULL if there are no more.
 */
struct wb *
wb_prev(struct wb *node)
{

	return wb_iter(node, 0);
}

/*
 * wb_delete
 *
 *	Delete node from the tree rooted at *rootp.
 */
void
wb_delete(struct wb **rootp, struct wb *node)
{

	delete(rootp, node);
}

/*
 * wb_delete_first
 *
 *	Delete the leftmost node from the tree rooted at *rootp and
 *	return it, or return NULL if the tree is empty.
 */
struct wb *
wb_delete_first(struct wb **rootp)
{
	struct wb *pp, *p, *n, *c;

	/* If the tree is empty, return NULL.  */
	if (*rootp == NULL)
		return NULL;

	/*
	 * Otherwise, find the leftmost node, invalidate it, and detach
	 * it.
	 */
	for (p = NULL, n = *rootp; (c = n->wb_child[0]) != NULL; p = n, n = c)
		continue;
	invalidate(n);
	detach(p, 0, n, node_ptr(rootp, p, 0));

	/*
	 * If the leftmost node had a child in the right direction,
	 * detach the child and replace this node by it.
	 */
	if ((c = n->wb_child[1]) != NULL) {
		detach(n, 1, c, &n->wb_child[1]);
		attach(p, 0, c, node_ptr(rootp, p, 0));
	}

	/*
	 * Adjust the tree from the bottom up to the root:
	 * - Decrement each ancestor's size.
	 * - Rotate if necessary.
	 */
	for (; p != NULL; p = pp) {
		pp = p->wb_parent;
		wb_assert(node_dir(p) == 0);
		wb_assert(0 < node_size(p));
		p->wb_size_dir--;
		wb_assert(nearbalanced_child(p, 1));
		if (unbalanced_child(p, 1))
			rotate(node_ptr(rootp, pp, 0), 1);
	}

	return n;
}

/*
 * wb_delete_last
 *
 *	Delete the rightmost node from the tree rooted at *rootp and
 *	return it, or return NULL if the tree is empty.
 */
struct wb *
wb_delete_last(struct wb **rootp)
{
	struct wb *pp, *p, *n, *c;
	unsigned dir;		/* 0 if root, 1 if not */

	/* If the tree is empty, return NULL.  */
	if (*rootp == NULL)
		return NULL;

	/*
	 * Otherwise, find the rightmost node, invalidate it, and
	 * detach it.
	 */
	for (p = NULL, n = *rootp; (c = n->wb_child[1]) != NULL; p = n, n = c)
		continue;
	invalidate(n);
	dir = node_dir(n);
	detach(p, dir, n, node_ptr(rootp, p, dir));

	/*
	 * If the rightmost node had a child in the left direction,
	 * detach the child and replace this node by it.
	 */
	if ((c = n->wb_child[0]) != NULL) {
		detach(n, 0, c, &n->wb_child[0]);
		attach(p, dir, c, node_ptr(rootp, p, dir));
	}

	/*
	 * Adjust the tree from the bottom up to the root:
	 * - Decrement each ancestor's size.
	 * - Rotate if necessary.
	 */
	for (; p != NULL; p = pp) {
		pp = p->wb_parent;
		dir = node_dir(p);
		wb_assert(pp == NULL || dir != 0);
		wb_assert(0 < node_size(p));
		p->wb_size_dir--;
		wb_assert(nearbalanced_child(p, 0));
		if (unbalanced_child(p, 0))
			rotate(node_ptr(rootp, pp, dir), 0);
	}

	return n;
}

/*
 * wb_find_at
 *
 *	Return the ith node in the sequence of nodes in the subtree
 *	rooted at root.
 */
struct wb *
wb_find_at(struct wb *root, size_t i)
{
	struct wb *n;
	unsigned dir;

	wb_assert(i < node_size(root));

	/* Descend the tree.  */
	for (n = root;; n = n->wb_child[dir]) {
		wb_assert(n != NULL);
		if (i < node_size(n->wb_child[0])) {
			/*
			 * Left of this one.  It's the ith node in the
			 * left child.
			 */
			dir = 0;
		} else if (node_size(n->wb_child[0]) < i) {
			/*
			 * Right of this one.  If the left child has k
			 * nodes, and this one represents 1, it's the
			 * jth node of the right child, where
			 *
			 *	j = i - k - 1.
			 */
			i -= node_size(n->wb_child[0]);
			i -= 1;
			dir = 1;
		} else {
			/* Found it.  Return it.  */
			return n;
		}
	}
}

/*
 * wb_insert_at
 *
 *	Insert node before the ith node in the sequence of nodes in the
 *	tree rooted at *rootp, or, if i is equal to the number of nodes
 *	in the tree, insert node at the end.
 */
void
wb_insert_at(struct wb **rootp, size_t i, struct wb *node)
{
	struct wb *p = NULL, *n;
	unsigned dir = 0;

	wb_assert(i <= node_size(*rootp));

	/* Descend the tree.  */
	for (n = *rootp; n != NULL; p = n, n = p->wb_child[dir]) {
		if (i <= node_size(n->wb_child[0])) {
			/*
			 * Insert left of this one, before the ith node
			 * in the left child.
			 */
			dir = 0;
		} else {
			/*
			 * Insert right of this one, before the jth
			 * node in the right child, where
			 *
			 *	j = i - k - 1,
			 *
			 * to account for the k nodes in the left child
			 * and one for this node.
			 */
			i -= node_size(n->wb_child[0]);
			i -= 1;
			dir = 1;
		}
	}

	/* Found the place to put it.  Insert it.  */
	insert(rootp, p, dir, node);
}

/*
 * wb_delete_at
 *
 *	Delete the ith node from the sequence of nodes in the tree
 *	rooted at *rootp.
 */
struct wb *
wb_delete_at(struct wb **rootp, size_t i)
{
	struct wb *p, *n;
	unsigned dir = 0;

	wb_assert(i < node_size(*rootp));

	/* Descend the tree.  */
	for (p = NULL, n = *rootp;; p = n, n = p->wb_child[dir]) {
		wb_assert(n != NULL);
		if (i < node_size(n->wb_child[0])) {
			/*
			 * Left of this one.  It's the ith node in the
			 * left child.
			 */
			dir = 0;
		} else if (node_size(n->wb_child[0]) < i) {
			/*
			 * Right of this one.  If the left child has k
			 * nodes, and this one represents 1, it's the
			 * jth node of the right child, where
			 *
			 *	j = i - k - 1.
			 */
			i -= node_size(n->wb_child[0]);
			i -= 1;
			dir = 1;
		} else {
			/* Found it.  Delete it and return it.  */
			delete(rootp, n);
			return n;
		}
	}
}

/*
 * wb_find_key_compare3
 *
 *	Find the node equivalent to key in the subtree rooted at node.
 *	compare(cookie, key, n) returns negative if key precedes the
 *	node n, positive if key follows it, or zero if they are
 *	equivalent.
 *
 *	If you have an efficient less-than relation, but no native
 *	three-way comparison, prefer wb_find_key_binary.
 *	Otherwise, wb_find_key_compare3 is guaranteed to require
 *	fewer calls to compare3 than the derived lt/gt algorithm.
 */
struct wb *
wb_find_key_compare3(struct wb *node, const void *key,
    int (*compare3)(void *, const void *, const struct wb *),
    void *cookie)
{
	struct wb *n;
	unsigned dir;

	/* Standard binary tree search with three-way compare.  */
	for (n = node; n != NULL; n = n->wb_child[dir]) {
		const int cmp3 = (*compare3)(cookie, key, n);

		if (cmp3 < 0)
			dir = 0;
		else if (0 < cmp3)
			dir = 1;
		else
			break;
	}

	return n;
}

/*
 * wb_find_key_binary
 *
 *	Find the node equivalent to key in the subtree rooted at node.
 *	lt(cookie, key, n) returns true if key precedes n; gt(cookie,
 *	key, n) returns true if key follows it.
 *
 *	If you have an efficient three-way comparison, prefer
 *	wb_find_key_compare3.  Otherwise, wb_find_key_binary is
 *	expected to require fewer calls to lt/gt than the derived
 *	compare3 algorithm.
 */
struct wb *
wb_find_key_binary(struct wb *node, const void *key,
    bool (*lt)(void *, const void *, const struct wb *),
    bool (*gt)(void *, const void *, const struct wb *),
    void *cookie)
{
	struct wb *n, *candidate = NULL;
	unsigned dir;

	/*
	 * Binary tree search with two-way compare.  Do exactly one
	 * compare at each node to find the leftmost node that could be
	 * it; then when we hit the bottom, make sure it matches.  The
	 * naive compare-low/compare-high search does either one or two
	 * comparisons at each node with 1/2 chance, so expected number
	 * of comparisons is 1.5*(d - 1) instead of d as we have here,
	 * for a tree of depth d.
	 */
	for (n = node; n != NULL; n = n->wb_child[dir]) {
		if ((*lt)(cookie, key, n)) {
			dir = 0;
		} else {
			candidate = n;
			dir = 1;
		}
	}
	if ((*gt)(cookie, key, candidate))
		return NULL;
	return candidate;
}

/*
 * wb_find_key_leq_compare3:
 *
 *	Find the first node less than or equal to key in the subtree
 *	rooted at node, or return NULL if there is none.
 */
struct wb *
wb_find_key_leq_compare3(struct wb *node, const void *key,
    int (*compare3)(void *, const void *, const struct wb *),
    void *cookie)
{
	struct wb *n, *candidate = NULL;
	unsigned dir;

	/* Standard binary tree search with three-way compare.  */
	for (n = node; n != NULL; n = n->wb_child[dir]) {
		const int cmp3 = (*compare3)(cookie, key, n);

		if (cmp3 < 0) {
			dir = 0;
		} else if (0 < cmp3) {
			candidate = n;
			dir = 1;
		} else {
			return n;
		}
	}

	return candidate;
}

/*
 * wb_find_key_leq_compare3:
 *
 *	Find the first node greater than or equal to key in the subtree
 *	rooted at node, or return NULL if there is none.
 */
struct wb *
wb_find_key_geq_compare3(struct wb *node, const void *key,
    int (*compare3)(void *, const void *, const struct wb *),
    void *cookie)
{
	struct wb *n, *candidate = NULL;
	unsigned dir;

	/* Standard binary tree search with three-way compare.  */
	for (n = node; n != NULL; n = n->wb_child[dir]) {
		const int cmp3 = (*compare3)(cookie, key, n);

		if (cmp3 < 0) {
			candidate = n;
			dir = 0;
		} else if (0 < cmp3) {
			dir = 1;
		} else {
			return n;
		}
	}

	return candidate;
}

/*
 * wb_insert_key_compare3
 *
 *	Insert node at the appropriate position in the sequence ordered
 *	by compare3.  compare3(cookie, n0, n1) returns negative if the
 *	node n0 precedes the node n1, positive if it follows, or zero
 *	if they are equivalent.  If there already is a node equivalent
 *	to node, leave the tree alone and return the equivalent node.
 *	Otherwise, return node.
 */
struct wb *
wb_insert_key_compare3(struct wb **rootp, struct wb *node,
    int (*compare3)(void *, const struct wb *, const struct wb *),
    void *cookie)
{
	struct wb *p, *n;
	unsigned dir = 0;

	/* Standard binary tree search with three-way compare.  */
	for (p = NULL, n = *rootp; n != NULL; p = n, n = p->wb_child[dir]) {
		const int cmp3 = (*compare3)(cookie, node, n);

		if (cmp3 < 0) {
			dir = 0;
		} else if (0 < cmp3) {
			dir = 1;
		} else {
			/* Collision: return the existing node.  */
			return n;
		}
	}

	/* Insert node and return it.  */
	insert(rootp, p, dir, node);
	return node;
}

/*
 * wb_replace_key_compare3
 *
 *	Insert node at the appropriate position in the sequence ordered
 *	by compare3.  compare3(cookie, n0, n1) returns negative if the
 *	node n0 precedes the node n1, positive if it follows, or zero
 *	if they are equivalent.  If there already is a node equivalent
 *	to node, remove the equivalent node from the tree and return
 *	it.  Otherwise, return node.
 */
struct wb *
wb_replace_key_compare3(struct wb **rootp, struct wb *node,
    int (*compare3)(void *, const struct wb *, const struct wb *),
    void *cookie)
{
	struct wb *p, *n, *c0, *c1;
	unsigned dir = 0;

	/* Standard binary tree search with three-way compare.  */
	for (p = NULL, n = *rootp; n != NULL; p = n, n = p->wb_child[dir]) {
		const int cmp3 = (*compare3)(cookie, node, n);

		if (cmp3 < 0)
			dir = 0;
		else if (0 < cmp3)
			dir = 1;
		else
			break;
	}

	/* If we didn't find a collision, insert node and return it.  */
	if (n == NULL) {
		insert(rootp, p, dir, node);
		return node;
	}

	/*
	 * Found a collision.
	 *
	 * - Detach the colliding node.
	 * - Detach its children.
	 */
	detach(p, dir, n, node_ptr(rootp, p, dir));
	c0 = n->wb_child[0];
	detach(n, 0, c0, &n->wb_child[0]);
	c1 = n->wb_child[1];
	detach(n, 1, c1, &n->wb_child[1]);

	/*
	 * Put node in its place.
	 *
	 * - Initialize node, and invalidate since it's not singleton.
	 * - Attach it where the collision was.
	 * - Attach the colliding node's children.
	 * - Revalidate node to calculate its size.
	 */
	node_init(node);
	invalidate(node);
	attach(p, dir, node, node_ptr(rootp, p, dir));
	attach(node, 0, c0, &node->wb_child[0]);
	attach(node, 1, c1, &node->wb_child[1]);
	revalidate(node);

	/* node's size and direction had better match the colliding node's.  */
	wb_assert(node->wb_size_dir == n->wb_size_dir);

	/* Invalidate, finalize, and return the colliding node.  */
	invalidate(n);
	node_fini(n);
	return n;
}
