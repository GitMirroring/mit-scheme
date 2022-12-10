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

#ifndef	WB_H
#define	WB_H

#include <stdbool.h>
#include <stddef.h>

struct wb {
	struct wb	*wb_child[2];
	struct wb	*wb_parent;
	size_t		wb_size_dir;
};

size_t		wb_size(struct wb *);
struct wb *	wb_first(struct wb *);
struct wb *	wb_last(struct wb *);
#define	WB_ITER_DESC	0
#define	WB_ITER_ASC	1
struct wb *	wb_iter_start(struct wb *, unsigned);
struct wb *	wb_iter(struct wb *, unsigned);
struct wb *	wb_next(struct wb *);
struct wb *	wb_prev(struct wb *);
void		wb_delete(struct wb **, struct wb *);
struct wb *	wb_delete_first(struct wb **);
struct wb *	wb_delete_last(struct wb **);
struct wb *	wb_find_at(struct wb *, size_t);
void		wb_insert_at(struct wb **, size_t, struct wb *);
struct wb *	wb_delete_at(struct wb **, size_t i);

struct wb *	wb_find_key_compare3(struct wb *, const void *,
		    int (*)(void *, const void *, const struct wb *),
		    void *);
struct wb *	wb_find_key_binary(struct wb *, const void *,
		    bool (*)(void *, const void *, const struct wb *),
		    bool (*)(void *, const void *, const struct wb *),
		    void *);
struct wb *	wb_find_key_leq_compare3(struct wb *, const void *,
		    int (*compare3)(void *, const void *, const struct wb *),
		    void *);
struct wb *	wb_find_key_geq_compare3(struct wb *, const void *,
		    int (*compare3)(void *, const void *, const struct wb *),
		    void *);
struct wb *	wb_insert_key_compare3(struct wb **, struct wb *,
		    int (*)(void *, const struct wb *, const struct wb *),
		    void *);
struct wb *	wb_replace_key_compare3(struct wb **, struct wb *,
		    int (*)(void *, const struct wb *, const struct wb *),
		    void *);

#endif	/* WB_H */
