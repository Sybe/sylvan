/*
 * Copyright 2011-2014 Formal Methods and Tools, University of Twente
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/* Do not include this file directly. Instead, include sylvan.h */

#ifndef SYLVAN_DDD_H
#define SYLVAN_DDD_H

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */


typedef uint64_t MDD;       // Note: low 40 bits only

#define dddmc_false         ((MDD)0)
#define dddmc_true          ((MDD)1)

/* Initialize LDD functionality */
void sylvan_init_ddd();

/* Primitives */
MDD dddmc_makenode(int32_t value, MDD ifeq, MDD ifneq, int8_t type, int8_t op);
//MDD lddmc_extendnode(MDD mdd, uint32_t value, MDD ifeq);
int32_t dddmc_getvalue(MDD mdd);
MDD dddmc_getdown(MDD mdd);
MDD dddmc_getright(MDD mdd);
MDD dddmc_follow(MDD mdd, int32_t value);

/**
 * Copy nodes in relations.
 * A copy node represents 'read x, then write x' for every x.
 * In a read-write relation, use copy nodes twice, once on read level, once on write level.
 * Copy nodes are only supported by relprod, relprev and union.
 */

/*For raw values*/
int32_t get_raw(int32_t value, int8_t op);
int32_t raw_get_value(int32_t raw);

/* Primitive for special 'copy node' (for relprod/relprev) */
MDD dddmc_make_copynode(MDD ifeq, MDD ifneq);
int dddmc_iscopy(MDD mdd);
MDD dddmc_followcopy(MDD mdd);

/* Add or remove external reference to MDD */
MDD dddmc_ref(MDD a);
void dddmc_deref(MDD a);

/* For use in custom mark functions */
VOID_TASK_DECL_1(dddmc_gc_mark_rec, MDD)
#define dddmc_gc_mark_rec(mdd) CALL(dddmc_gc_mark_rec, mdd)

/* Return the number of external references */
size_t dddmc_count_refs();

/* Mark MDD for "notify on dead" */
#define dddmc_notify_ondead(mdd) llmsset_notify_ondead(nodes, mdd)

/* Sanity check - returns depth of MDD including 'true' terminal or 0 for empty set */
#ifndef NDEBUG
size_t dddmc_test_ismdd(MDD mdd);
#endif

/* Operations for model checking */
TASK_DECL_2(MDD, dddmc_union, MDD, MDD);
#define dddmc_union(a, b) CALL(dddmc_union, a, b)

TASK_DECL_2(MDD, dddmc_nimp, MDD, MDD)
#define dddmc_nimp(a, b) CALL(dddmc_nimp, a, b)

TASK_DECL_2(MDD, dddmc_minus, MDD, MDD);
#define dddmc_minus(a, b) CALL(dddmc_minus, a, b)

TASK_DECL_3(MDD, dddmc_zip, MDD, MDD, MDD*);
#define dddmc_zip(a, b, res) CALL(dddmc_zip, a, b, res)

TASK_DECL_1(MDD, dddmc_complement, MDD);
#define dddmc_complement(a) CALL(dddmc_complement, a)

TASK_DECL_2(MDD, dddmc_intersect, MDD, MDD);
#define dddmc_intersect(a, b) CALL(dddmc_intersect, a, b)

TASK_DECL_2(MDD, dddmc_biimp, MDD, MDD);
#define dddmc_biimp(a, b) CALL(dddmc_biimp, a, b)

TASK_DECL_3(MDD, dddmc_match, MDD, MDD, MDD);
#define dddmc_match(a, b, proj) CALL(dddmc_match, a, b, proj)

TASK_DECL_4(MDD, dddmc_union_cube, MDD, int32_t*, size_t, int);
#define dddmc_union_cube(a, values, count, discrete_vars) CALL(dddmc_union_cube, a, values, count, discrete_vars)

TASK_DECL_1(int8_t, dddmc_tautology, MDD);
#define dddmc_tautology(a) CALL(dddmc_tautology, a)

TASK_DECL_1(int, dddmc_depth, MDD);
#define dddmc_depth(a) CALL(dddmc_depth, a)

TASK_DECL_2(int8_t, dddmc_equal, MDD, MDD);
#define dddmc_equal(a, b) CALL(dddmc_equal, a, b)


//MDD dddmc_union_cube(MDD a, uint32_t* values, size_t count);
int dddmc_member_cube(MDD a, int32_t* values, size_t count);
MDD dddmc_cube(int32_t* values, size_t count, int discrete_vars);

MDD dddmc_union_cube_copy(MDD a, int32_t* values, int* copy, size_t count);
int dddmc_member_cube_copy(MDD a, int32_t* values, int* copy, size_t count);
MDD dddmc_cube_copy(int32_t* values, int* copy, size_t count);

TASK_DECL_3(MDD, dddmc_relprod, MDD, MDD, MDD);
#define dddmc_relprod(a, b, proj) CALL(dddmc_relprod, a, b, proj)

TASK_DECL_4(MDD, dddmc_relprod_union, MDD, MDD, MDD, MDD);
#define dddmc_relprod_union(a, b, meta, un) CALL(dddmc_relprod_union, a, b, meta, un)

/**
 * Calculate all predecessors to a in uni according to rel[proj]
 * <proj> follows the same semantics as relprod
 * i.e. 0 (not in rel), 1 (read+write), 2 (read), 3 (write), -1 (end; rest=0)
 */
TASK_DECL_4(MDD, dddmc_relprev, MDD, MDD, MDD, MDD);
#define dddmc_relprev(a, rel, proj, uni) CALL(dddmc_relprev, a, rel, proj, uni)

// so: proj: -2 (end; quantify rest), -1 (end; keep rest), 0 (quantify), 1 (keep)
TASK_DECL_2(MDD, dddmc_project, MDD, MDD);
#define dddmc_project(mdd, proj) CALL(dddmc_project, mdd, proj)

TASK_DECL_3(MDD, dddmc_project_minus, MDD, MDD, MDD);
#define dddmc_project_minus(mdd, proj, avoid) CALL(dddmc_project_minus, mdd, proj, avoid)

TASK_DECL_4(MDD, dddmc_join, MDD, MDD, MDD, MDD);
#define dddmc_join(a, b, a_proj, b_proj) CALL(dddmc_join, a, b, a_proj, b_proj)

MDD dddmc_reduce(MDD a, int clocks);

/* Write a DOT representation */
void dddmc_printdot(MDD mdd);
void dddmc_fprintdot(FILE *out, MDD mdd);

void dddmc_fprint(FILE *out, MDD mdd);
void dddmc_print(MDD mdd);

void dddmc_printsha(MDD mdd);
void dddmc_fprintsha(FILE *out, MDD mdd);
void dddmc_getsha(MDD mdd, char *target); // at least 65 bytes...

/**
 * Calculate number of satisfying variable assignments.
 * The set of variables must be >= the support of the MDD.
 * (i.e. all variables in the MDD must be in variables)
 *
 * The cached version uses the operation cache, but is limited to 64-bit floating point numbers.
 */

typedef double dddmc_satcount_double_t;
// if this line below gives an error, modify the above typedef until fixed ;)
typedef char __dddmc_check_float_is_8_bytes[(sizeof(dddmc_satcount_double_t) == sizeof(uint64_t))?1:-1];

TASK_DECL_1(dddmc_satcount_double_t, dddmc_satcount_cached, MDD);
#define dddmc_satcount_cached(mdd) CALL(dddmc_satcount_cached, mdd)

TASK_DECL_1(long double, dddmc_satcount, MDD);
#define dddmc_satcount(mdd) CALL(dddmc_satcount, mdd)

/**
 * A callback for enumerating functions like sat_all_par, collect and match
 * Example:
 * TASK_3(void*, my_function, uint32_t*, values, size_t, count, void*, context) ...
 * For collect, use:
 * TASK_3(MDD, ...)
 */
LACE_TYPEDEF_CB(void, dddmc_enum_cb, int32_t*, size_t, void*);
LACE_TYPEDEF_CB(MDD, dddmc_collect_cb, int32_t*, size_t, void*);

VOID_TASK_DECL_5(dddmc_sat_all_par, MDD, dddmc_enum_cb, void*, int32_t*, size_t);
#define dddmc_sat_all_par(mdd, cb, context) CALL(dddmc_sat_all_par, mdd, cb, context, 0, 0)

VOID_TASK_DECL_4(dddmc_sat_all_nopar, MDD, dddmc_enum_cb, int, void*);
#define dddmc_sat_all_nopar(mdd, cb, count, context) CALL(dddmc_sat_all_nopar, mdd, cb, count, context)

TASK_DECL_5(MDD, dddmc_collect, MDD, dddmc_collect_cb, void*, int32_t*, size_t);
#define dddmc_collect(mdd, cb, context) CALL(dddmc_collect, mdd, cb, context, 0, 0)

VOID_TASK_DECL_5(dddmc_match_sat_par, MDD, MDD, MDD, dddmc_enum_cb, void*);
#define dddmc_match_sat_par(mdd, match, proj, cb, context) CALL(dddmc_match_sat_par, mdd, match, proj, cb, context)

int dddmc_sat_one(MDD mdd, int32_t *values, size_t count);
MDD dddmc_sat_one_mdd(MDD mdd);
#define dddmc_pick_cube dddmc_sat_one_mdd

/**
 * Callback functions for visiting nodes.
 * lddmc_visit_seq sequentially visits nodes, down first, then right.
 * lddmc_visit_par visits nodes in parallel (down || right)
 */
LACE_TYPEDEF_CB(int, dddmc_visit_pre_cb, MDD, void*); // int pre(MDD, context)
LACE_TYPEDEF_CB(void, dddmc_visit_post_cb, MDD, void*); // void post(MDD, context)
LACE_TYPEDEF_CB(void, dddmc_visit_init_context_cb, void*, void*, int); // void init_context(context, parent, is_down)

//typedef struct lddmc_visit_node_callbacks {
//    lddmc_visit_pre_cb lddmc_visit_pre;
//    lddmc_visit_post_cb lddmc_visit_post;
//    lddmc_visit_init_context_cb lddmc_visit_init_context;
//} lddmc_visit_callbacks_t;

VOID_TASK_DECL_4(dddmc_visit_par, MDD, lddmc_visit_callbacks_t*, size_t, void*);
#define dddmc_visit_par(mdd, cbs, ctx_size, context) CALL(dddmc_visit_par, mdd, cbs, ctx_size, context);

VOID_TASK_DECL_4(dddmc_visit_seq, MDD, lddmc_visit_callbacks_t*, size_t, void*);
#define dddmc_visit_seq(mdd, cbs, ctx_size, context) CALL(dddmc_visit_seq, mdd, cbs, ctx_size, context);

size_t dddmc_nodecount(MDD mdd);
void dddmc_nodecount_levels(MDD mdd, size_t *variables);

/**
 * Functional composition
 * For every node at depth <depth>, call function cb (MDD -> MDD).
 * and replace the node by the result of the function
 */
LACE_TYPEDEF_CB(MDD, dddmc_compose_cb, MDD, void*);
TASK_DECL_4(MDD, dddmc_compose, MDD, dddmc_compose_cb, void*, int);
#define dddmc_compose(mdd, cb, context, depth) CALL(dddmc_compose, mdd, cb, context, depth)

/**
 * SAVING:
 * use lddmc_serialize_add on every MDD you want to store
 * use lddmc_serialize_get to retrieve the key of every stored MDD
 * use lddmc_serialize_tofile
 *
 * LOADING:
 * use lddmc_serialize_fromfile (implies lddmc_serialize_reset)
 * use lddmc_serialize_get_reversed for every key
 *
 * MISC:
 * use lddmc_serialize_reset to free all allocated structures
 * use lddmc_serialize_totext to write a textual list of tuples of all MDDs.
 *         format: [(<key>,<level>,<key_low>,<key_high>,<complement_high>),...]
 *
 * for the old lddmc_print functions, use lddmc_serialize_totext
 */
size_t dddmc_serialize_add(MDD mdd);
size_t dddmc_serialize_get(MDD mdd);
MDD dddmc_serialize_get_reversed(size_t value);
void dddmc_serialize_reset();
void dddmc_serialize_totext(FILE *out);
void dddmc_serialize_tofile(FILE *out);
void dddmc_serialize_fromfile(FILE *in);

/* Infrastructure for internal markings */
typedef struct dddmc_refs_internal
{
    size_t r_size, r_count;
    size_t s_size, s_count;
    MDD *results;
    Task **spawns;
} *dddmc_refs_internal_t;

extern DECLARE_THREAD_LOCAL(dddmc_refs_key, dddmc_refs_internal_t);
//TODO
static inline MDD
dddmc_refs_push(MDD ldd)
{
    LOCALIZE_THREAD_LOCAL(dddmc_refs_key, dddmc_refs_internal_t);
    if (dddmc_refs_key->r_count >= dddmc_refs_key->r_size) {
        dddmc_refs_key->r_size *= 2;
        dddmc_refs_key->results = (MDD*)realloc(dddmc_refs_key->results, sizeof(MDD) * dddmc_refs_key->r_size);
    }
    dddmc_refs_key->results[dddmc_refs_key->r_count++] = ldd;
    return ldd;
}
//TODO
static inline void
dddmc_refs_pop(int amount)
{
    LOCALIZE_THREAD_LOCAL(dddmc_refs_key, dddmc_refs_internal_t);
    dddmc_refs_key->r_count-=amount;
}
//TODO
static inline void
dddmc_refs_spawn(Task *t)
{
    LOCALIZE_THREAD_LOCAL(dddmc_refs_key, dddmc_refs_internal_t);
    if (dddmc_refs_key->s_count >= dddmc_refs_key->s_size) {
        dddmc_refs_key->s_size *= 2;
        dddmc_refs_key->spawns = (Task**)realloc(dddmc_refs_key->spawns, sizeof(Task*) * dddmc_refs_key->s_size);
    }
    dddmc_refs_key->spawns[dddmc_refs_key->s_count++] = t;
}
//TODO
static inline MDD
dddmc_refs_sync(MDD result)
{
    LOCALIZE_THREAD_LOCAL(dddmc_refs_key, dddmc_refs_internal_t);
    dddmc_refs_key->s_count--;
    return result;
}

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif
