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

#include <sylvan_config.h>

#include <assert.h>
#include <inttypes.h>
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//#include <avl.h>
#include <refs.h>
#include <sha2.h>
#include <sylvan.h>
#include <sylvan_common.h>

/**
 * DDD node structure
 */
typedef struct __attribute__((packed)) mddnode {
    uint64_t a, b;
} * mddnode_t; // 16 bytes

// RmRR RRRR RRRR VVVV | VVVV DcDD DDDD DDDD (little endian - in memory)
// VVVV RRRR RRRR RRRm | DDDD DDDD DDDc VVVV (big endian)

// Ensure our dddnode is 16 bytes
typedef char __dddmc_check_mddnode_t_is_16_bytes[(sizeof(struct mddnode)==16) ? 1 : -1];

//TODO define this well;
int32_t LE_INFTY = 2147483646;

int32_t raw_get_value(int32_t raw){
    return raw >> 1;
}

int8_t raw_get_op(int32_t raw){
    return raw & 0x1;
}

int32_t get_raw(int32_t value, int8_t op){
    return (value << 1) | op;
}

static inline int32_t __attribute__((unused))
dddnode_getvalue(mddnode_t n)
{
    return *(int32_t*)((uint8_t*)n+6);
}

static inline uint8_t __attribute__((unused))
dddnode_getmark(mddnode_t n)
{
    return n->a & 1;
}

static inline uint8_t __attribute__((unused))
dddnode_getcopy(mddnode_t n)
{
    return n->b & 0x10000 ? 1 : 0;
}
//0 is standard LDD node
//1 is DDD node
static inline int8_t __attribute__((unused))
dddnode_gettype(mddnode_t n)
{
    return n->a & 0x800000000000 ? 1 : 0;
}
//0 is <
//1 is <=
static inline int8_t __attribute__((unused))
dddnode_getop(mddnode_t n)
{
    return n->a & 0x400000000000 ? 1 : 0;
}

static inline uint64_t __attribute__((unused))
dddnode_getright(mddnode_t n)
{
    return (n->a & 0x000000ffffffffff) >> 1;
}

static inline uint64_t __attribute__((unused))
dddnode_getdown(mddnode_t n)
{
    return n->b >> 17;
}
static inline void __attribute__((unused))
dddnode_setvalue(mddnode_t n, int32_t value)
{
    *(int32_t*)((uint8_t*)n+6) = value;
}

static inline void __attribute__((unused))
dddnode_setmark(mddnode_t n, uint8_t mark)
{
    n->a = (n->a & 0xfffffffffffffffe) | (mark ? 1 : 0);
}

static inline void __attribute__((unused))
dddnode_settype(mddnode_t n, int8_t type)
{
    n->a = (n->a & 0xffff7fffffffffff) | ((uint64_t)type << 47);
}

static inline void __attribute__((unused))
dddnode_setop(mddnode_t n, int8_t op)
{
    n->a = (n->a & 0xffffbfffffffffff) | ((uint64_t)op << 46);
}

static inline void __attribute__((unused))
dddnode_setright(mddnode_t n, uint64_t right)
{
    n->a = (n->a & 0xffffc00000000001) | (right << 1);
}

static inline void __attribute__((unused))
dddnode_setdown(mddnode_t n, uint64_t down)
{
    n->b = (n->b & 0x000000000001ffff) | (down << 17);
}

static inline void __attribute__((unused))
dddnode_make(mddnode_t n, int32_t value, uint64_t right, uint64_t down, int8_t type, int8_t op)
{
    n->a = right << 1;
    n->b = down << 17;
    dddnode_setop(n, op);
    dddnode_settype(n, type);
    *(int32_t*)((uint8_t*)n+6) = value;
}

static inline void __attribute__((unused))
dddnode_makecopy(mddnode_t n, uint64_t right, uint64_t down, int8_t type, int8_t op)
{
    n->a = right << 1;
    n->b = ((down << 1) | 1) << 16;
    dddnode_setop(n, op);
    dddnode_settype(n, type);
}

#define GETNODE(mdd) ((mddnode_t)llmsset_index_to_ptr(nodes, mdd))

/**
 * Implementation of garbage collection
 */

/* Recursively mark MDD nodes as 'in use' */
VOID_TASK_IMPL_1(dddmc_gc_mark_rec, MDD, mdd)
{
    if (mdd <= dddmc_true) return;

    if (llmsset_mark(nodes, mdd)) {
        mddnode_t n = GETNODE(mdd);
        SPAWN(dddmc_gc_mark_rec, dddnode_getright(n));
        CALL(dddmc_gc_mark_rec, dddnode_getdown(n));
        SYNC(dddmc_gc_mark_rec);
    }
}

/**
 * External references
 */

refs_table_t mdd_refs;

MDD
dddmc_ref(MDD a)
{
    if (a == dddmc_true || a == dddmc_false) return a;
    refs_up(&mdd_refs, a);
    return a;
}

void
dddmc_deref(MDD a)
{
    if (a == dddmc_true || a == dddmc_false) return;
    refs_down(&mdd_refs, a);
}

size_t
dddmc_count_refs()
{
    return refs_count(&mdd_refs);
}
//TODO
/* Called during garbage collection */
VOID_TASK_0(dddmc_gc_mark_external_refs)
{
    // iterate through refs hash table, mark all found
    size_t count=0;
    uint64_t *it = refs_iter(&mdd_refs, 0, mdd_refs.refs_size);
    while (it != NULL) {
        SPAWN(dddmc_gc_mark_rec, refs_next(&mdd_refs, &it, mdd_refs.refs_size));
        count++;
    }
    while (count--) {
        SYNC(dddmc_gc_mark_rec);
    }
}

/* Infrastructure for internal markings */
DECLARE_THREAD_LOCAL(dddmc_refs_key, dddmc_refs_internal_t);

VOID_TASK_0(dddmc_refs_mark_task)
{
    LOCALIZE_THREAD_LOCAL(dddmc_refs_key, dddmc_refs_internal_t);
    size_t i, j=0;
    for (i=0; i<dddmc_refs_key->r_count; i++) {
        if (j >= 40) {
            while (j--) SYNC(dddmc_gc_mark_rec);
            j=0;
        }
        SPAWN(dddmc_gc_mark_rec, dddmc_refs_key->results[i]);
        j++;
    }
    for (i=0; i<dddmc_refs_key->s_count; i++) {
        Task *t = dddmc_refs_key->spawns[i];
        if (!TASK_IS_STOLEN(t)) break;
        if (TASK_IS_COMPLETED(t)) {
            if (j >= 40) {
                while (j--) SYNC(dddmc_gc_mark_rec);
                j=0;
            }
            SPAWN(dddmc_gc_mark_rec, *(BDD*)TASK_RESULT(t));
            j++;
        }
    }
    while (j--) SYNC(dddmc_gc_mark_rec);
}

VOID_TASK_0(dddmc_refs_mark)
{
    TOGETHER(dddmc_refs_mark_task);
}

VOID_TASK_0(dddmc_refs_init_task)
{
    dddmc_refs_internal_t s = (dddmc_refs_internal_t)malloc(sizeof(struct dddmc_refs_internal));
    s->r_size = 128;
    s->r_count = 0;
    s->s_size = 128;
    s->s_count = 0;
    s->results = (BDD*)malloc(sizeof(BDD) * 128);
    s->spawns = (Task**)malloc(sizeof(Task*) * 128);
    SET_THREAD_LOCAL(dddmc_refs_key, s);
}

VOID_TASK_0(dddmc_refs_init)
{
    INIT_THREAD_LOCAL(dddmc_refs_key);
    TOGETHER(dddmc_refs_init_task);
    sylvan_gc_add_mark(10, TASK(dddmc_refs_mark));
}

/**
 * Initialize and quit functions
 */

static void
dddmc_quit()
{
    refs_free(&mdd_refs);
}

void
sylvan_init_ddd()
{
    sylvan_register_quit(dddmc_quit);
    sylvan_gc_add_mark(10, TASK(dddmc_gc_mark_external_refs));

    // Sanity check
    if (sizeof(struct mddnode) != 16) {
        fprintf(stderr, "Invalid size of mdd nodes: %ld\n", sizeof(struct mddnode));
        exit(1);
    }

    refs_create(&mdd_refs, 1024);

    LACE_ME;
    CALL(dddmc_refs_init);
}

/**
 * Primitives
 */
MDD
dddmc_makenode(int32_t value, MDD ifeq, MDD ifneq, int8_t type, int8_t op)
{
    if (ifeq == dddmc_false && type == 0) return ifneq;
    if (ifeq == dddmc_false && ifneq == dddmc_false) return dddmc_false;
    if (ifeq == dddmc_true && ifneq == dddmc_true) return dddmc_true;
    if (ifeq == dddmc_false && type == 1 && ifneq != dddmc_false && ifneq != dddmc_true) return ifneq;


    // check if correct (should be false, or next in value)
//    assert(ifneq != dddmc_true);

    if (ifneq != dddmc_false && ifneq != dddmc_true) assert(value <= dddnode_getvalue(GETNODE(ifneq)));

    if(type){
        if(ifeq == dddmc_getdown(ifneq)){
            return ifneq;
        }
    }

    struct mddnode n;
    dddnode_make(&n, value, ifneq, ifeq, type, op);

    int created;
    uint64_t index = llmsset_lookup(nodes, n.a, n.b, &created);
    if (index == 0) {
        dddmc_refs_push(ifeq);
        dddmc_refs_push(ifneq);
        LACE_ME;
        sylvan_gc();
        dddmc_refs_pop(1);

        index = llmsset_lookup(nodes, n.a, n.b, &created);
        if (index == 0) {
            fprintf(stderr, "MDD Unique table full, %zu of %zu buckets filled!\n", llmsset_count_marked(nodes), llmsset_get_size(nodes));
            exit(1);
        }
    }

    if (created) sylvan_stats_count(LDD_NODES_CREATED);
    else sylvan_stats_count(LDD_NODES_REUSED);

    return (MDD)index;
}
//TODO
MDD
dddmc_make_copynode(MDD ifeq, MDD ifneq)
{
    struct mddnode n;
    dddnode_makecopy(&n, ifneq, ifeq, 0, 0);

    int created;
    uint64_t index = llmsset_lookup(nodes, n.a, n.b, &created);
    if (index == 0) {
        dddmc_refs_push(ifeq);
        dddmc_refs_push(ifneq);
        LACE_ME;
        sylvan_gc();
        dddmc_refs_pop(1);

        index = llmsset_lookup(nodes, n.a, n.b, &created);
        if (index == 0) {
            fprintf(stderr, "MDD Unique table full, %zu of %zu buckets filled!\n", llmsset_count_marked(nodes), llmsset_get_size(nodes));
            exit(1);
        }
    }

    if (created) sylvan_stats_count(LDD_NODES_CREATED);
    else sylvan_stats_count(LDD_NODES_REUSED);

    return (MDD)index;
}

//MDD
//lddmc_extendnode(MDD mdd, uint32_t value, MDD ifeq)
//{
//    if (mdd <= lddmc_true) return lddmc_makenode(value, ifeq, mdd);
//
//    mddnode_t n = GETNODE(mdd);
//    if (mddnode_getcopy(n)) return lddmc_make_copynode(mddnode_getdown(n), lddmc_extendnode(mddnode_getright(n), value, ifeq));
//    uint32_t n_value = mddnode_getvalue(n);
//    if (n_value < value) return lddmc_makenode(n_value, mddnode_getdown(n), lddmc_extendnode(mddnode_getright(n), value, ifeq));
//    if (n_value == value) return lddmc_makenode(value, ifeq, mddnode_getright(n));
//    /* (n_value > value) */ return lddmc_makenode(value, ifeq, mdd);
//}

int32_t
dddmc_getvalue(MDD mdd)
{
    return dddnode_getvalue(GETNODE(mdd));
}

MDD
dddmc_getdown(MDD mdd)
{
    return dddnode_getdown(GETNODE(mdd));
}

MDD
dddmc_getright(MDD mdd)
{
    return dddnode_getright(GETNODE(mdd));
}

//TODO hier onderscheid maken tussen DDD en LDD nodes
MDD
dddmc_follow(MDD mdd, int32_t value)
{
    mddnode_t na = GETNODE(mdd);
    uint8_t type = dddnode_gettype(na);
    if(!type){
        for (;;) {
            if (mdd <= dddmc_true) return mdd;
            const mddnode_t n = GETNODE(mdd);
            if (!dddnode_getcopy(n)) {
                const int32_t v = dddnode_getvalue(n);
                if (v == value) return dddnode_getdown(n);
                if (v > value) return dddmc_false;
            }
            mdd = dddnode_getright(n);
        }
    } else {//DDD node
        int8_t value_op = raw_get_op(value);
        int32_t value_value = raw_get_value(value);
        for (;;) {
            na = GETNODE(mdd);
            int8_t na_op = dddnode_getop(na);
            int8_t na_value = dddnode_getvalue(na);
            if (mdd <= dddmc_true) return mdd;
            if (!dddnode_getcopy(na)) {
                const int32_t v = na_value;
                if (v > value_value) return dddnode_getdown(na);
                if (v == value_value && (value_op == na_op || na_op == 1)) return dddnode_getdown(na);
            }
            mdd = dddnode_getright(na);
        }
    }
}

//int
//lddmc_iscopy(MDD mdd)
//{
//    if (mdd <= lddmc_true) return 0;
//
//    mddnode_t n = GETNODE(mdd);
//    return mddnode_getcopy(n) ? 1 : 0;
//}

//MDD
//lddmc_followcopy(MDD mdd)
//{
//    if (mdd <= lddmc_true) return lddmc_false;
//
//    mddnode_t n = GETNODE(mdd);
//    if (mddnode_getcopy(n)) return mddnode_getdown(n);
//    else return lddmc_false;
//}

/**
 * MDD operations
 */
void floyd_warshall(int32_t* M, int clocks){
    for(int k = 0; k < clocks; k++){
        for(int i = 0; i < clocks; i++){
            for(int j = 0; j < clocks; j++){
                if(raw_get_value(M[clocks * i + j]) > raw_get_value(M[clocks * i + k]) + raw_get_value(M[clocks * k + j])){
                    M[clocks * i + j] = get_raw(raw_get_value(M[clocks * i + k]) + raw_get_value(M[clocks * k + j]), raw_get_op(M[clocks * i + j]));
                }
            }
        }
    }
}


int feasible(int32_t* M, int clocks){
    floyd_warshall(M, clocks);
    for(int i = 0; i < clocks; i++){
        int32_t value = raw_get_value(M[i + clocks * i]);
        //if(value < 0 || (value == 0 && op == 0)){
        if(value < 0){
            return 0;
        }
    }
    return 1;
}


MDD
_dddmc_reduce(MDD a, int clocks, int32_t* M, int level)
{
    mddnode_t na = GETNODE(a);
    if(level%(clocks + 1) == 0) level++;
    if(!feasible(M, clocks)){
        fprintf(stdout, "return dddmc_false\n");
        fflush(stdout);
        return dddmc_false;
    } else if (a == dddmc_false || a == dddmc_true){
        return a;
    } else {
        MDD result;
        int32_t* M_h = malloc(clocks*clocks * sizeof(int32_t));
        int32_t* M_l = malloc(clocks*clocks * sizeof(int32_t));
        memcpy(M_h, M, clocks*clocks * sizeof(int32_t));
        memcpy(M_l, M, clocks*clocks * sizeof(int32_t));
        M_h[level] = get_raw(dddmc_getvalue(a), dddnode_getop(na));
        M_l[level] = get_raw(-dddmc_getvalue(a), dddnode_getop(na));
        MDD h = _dddmc_reduce(dddmc_getdown(a), clocks, M_h, level++);
        MDD l = _dddmc_reduce(dddmc_getright(a), clocks, M_l, level);
        if(l != dddmc_false && h != dddmc_false){
            result = dddmc_makenode(dddmc_getvalue(a), h, l, 1, dddnode_getop(na));
        } else if (h != dddmc_false){
            result = dddmc_makenode(raw_get_value(LE_INFTY), h, dddmc_false, 1, raw_get_op(LE_INFTY));
        } else {
            result = l;
        }
        return result;
    }
}


MDD
dddmc_reduce(MDD a, int clocks)
{
    if(a == dddmc_true || a == dddmc_false) return a;
    mddnode_t na = GETNODE(a);
    int8_t type = dddnode_gettype(na);
    if(!type){
        MDD down = dddmc_reduce(dddnode_getdown(na), clocks);
        MDD right = dddmc_reduce(dddnode_getright(na), clocks);
        return dddmc_makenode(dddnode_getvalue(na), down, right, 0, 0);
    }
    MDD result;
    int32_t M[clocks*clocks];
    for(int i = 0; i < clocks*clocks; i++){
        M[i] = LE_INFTY;
    }
    result = _dddmc_reduce(a, clocks, M, 0);
    return result;
}



static inline int
match_ddds(MDD *one, MDD *two)
{
    MDD m1 = *one, m2 = *two;
    if (m1 == dddmc_false || m2 == dddmc_false) return 0;
    mddnode_t n1 = GETNODE(m1), n2 = GETNODE(m2);
    int32_t v1 = dddnode_getvalue(n1), v2 = dddnode_getvalue(n2);
    int8_t type = dddnode_gettype(n1);
    if(!type){
        while (v1 != v2) {
            if (v1 < v2) {
                m1 = dddnode_getright(n1);
                if (m1 == dddmc_false) return 0;
                n1 = GETNODE(m1);
                v1 = dddnode_getvalue(n1);
            } else if (v1 > v2) {
                m2 = dddnode_getright(n2);
                if (m2 == dddmc_false) return 0;
                n2 = GETNODE(m2);
                v2 = dddnode_getvalue(n2);
            }
        }
    } else {
        int8_t n2_type = dddnode_gettype(n2);
        if(!n2_type){
            int8_t n1_op = dddnode_getop(n1);
            int32_t n1_val = dddnode_getvalue(n1);
            int32_t raw_n2_val = dddnode_getvalue(n2);
            int32_t n2_val = raw_get_value(raw_n2_val);
            int32_t n2_op = raw_get_op(raw_n2_val);
            while(n1_val != n2_val && n1_op != n2_op) {
                if(n1_val < n2_val) {
                    m1 = dddnode_getright(n1);
                    if (m1 == dddmc_false) return 0;
                    n1 = GETNODE(m1);
                    n1_val = dddnode_getvalue(n1);
                    n1_op = dddnode_getop(n1);
                } else if (n1_val > n2_val){
                    m2 = dddnode_getright(n2);
                    if (m2 == dddmc_false) return 0;
                    n2 = GETNODE(m2);
                    raw_n2_val = dddnode_getvalue(n2);
                    n2_val = raw_get_value(raw_n2_val);
                    n2_op = raw_get_op(raw_n2_val);
                } else if (n1_op < n2_op){//values equal
                    m1 = dddnode_getright(n1);
                    if (m1 == dddmc_false) return 0;
                    n1 = GETNODE(m1);
                    n1_val = dddnode_getvalue(n1);
                    n1_op = dddnode_getop(n1);
                } else if (n2_op > n1_op){
                    m2 = dddnode_getright(n2);
                    if (m2 == dddmc_false) return 0;
                    n2 = GETNODE(m2);
                    raw_n2_val = dddnode_getvalue(n2);
                    n2_val = raw_get_value(raw_n2_val);
                    n2_op = raw_get_op(raw_n2_val);
                }
            }
        } else {
            int8_t n1_op = dddnode_getop(n1);
            int32_t n1_val = dddnode_getvalue(n1);
            int32_t n2_val = dddnode_getvalue(n2);
            int32_t n2_op = dddnode_getop(n2);
            while(n1_val != n2_val && n1_op != n2_op) {
                if(n1_val < n2_val) {
                    m1 = dddnode_getright(n1);
                    if (m1 == dddmc_false) return 0;
                    n1 = GETNODE(m1);
                    n1_val = dddnode_getvalue(n1);
                    n1_op = dddnode_getop(n1);
                } else if (n1_val > n2_val){
                    m2 = dddnode_getright(n2);
                    if (m2 == dddmc_false) return 0;
                    n2 = GETNODE(m2);
                    n2_val = dddnode_getvalue(n2);
                    n2_op = dddnode_getop(n2);
                } else if (n1_op < n2_op){//values equal
                    m1 = dddnode_getright(n1);
                    if (m1 == dddmc_false) return 0;
                    n1 = GETNODE(m1);
                    n1_val = dddnode_getvalue(n1);
                    n1_op = dddnode_getop(n1);
                } else if (n2_op > n1_op){
                    m2 = dddnode_getright(n2);
                    if (m2 == dddmc_false) return 0;
                    n2 = GETNODE(m2);
                    n2_val = dddnode_getvalue(n2);
                    n2_op = dddnode_getop(n2);
                }
            }
        }
    }
    *one = m1;
    *two = m2;
    return 1;
}

static inline int
match_set_rel_ddds(MDD *set, MDD *rel)
{
    MDD m1 = *set, m2 = *rel;
    if (m1 == dddmc_false || m2 == dddmc_false) return 0;
    mddnode_t n1 = GETNODE(m1), n2 = GETNODE(m2);
    int8_t type = dddnode_gettype(n1);
    if(!type){
        int32_t v1 = dddnode_getvalue(n1), v2 = dddnode_getvalue(n2);
        while (v1 != v2) {
            if (v1 < v2) {
                m1 = dddnode_getright(n1);
                if (m1 == dddmc_false) return 0;
                n1 = GETNODE(m1);
                v1 = dddnode_getvalue(n1);
            } else if (v1 > v2) {
                m2 = dddnode_getright(n2);
                if (m2 == dddmc_false) return 0;
                n2 = GETNODE(m2);
                v2 = dddnode_getvalue(n2);
            }
        }
    } else {
        int8_t set_op = dddnode_getop(n1);
        int32_t set_val = dddnode_getvalue(n1);
        int32_t raw_rel_val = dddnode_getvalue(n2);
        int32_t rel_val = raw_get_value(raw_rel_val);
        int32_t rel_op = raw_get_op(raw_rel_val);
        while(set_val != rel_val && set_op != rel_op) {
            if(set_val < rel_val) {
                m1 = dddnode_getright(n1);
                if (m1 == dddmc_false) return 0;
                n1 = GETNODE(m1);
                set_val = dddnode_getvalue(n1);
                set_op = dddnode_getop(n1);
            } else if (set_val > rel_val){
                m2 = dddnode_getright(n2);
                if (m2 == dddmc_false) return 0;
                n2 = GETNODE(m2);
                raw_rel_val = dddnode_getvalue(n2);
                rel_val = raw_get_value(raw_rel_val);
                rel_op = raw_get_op(raw_rel_val);
            } else if (set_op < rel_op){//values equal
                m1 = dddnode_getright(n1);
                if (m1 == dddmc_false) return 0;
                n1 = GETNODE(m1);
                set_val = dddnode_getvalue(n1);
                set_op = dddnode_getop(n1);
            } else if (rel_op < set_op){
                m2 = dddnode_getright(n2);
                if (m2 == dddmc_false) return 0;
                n2 = GETNODE(m2);
                raw_rel_val = dddnode_getvalue(n2);
                rel_val = raw_get_value(raw_rel_val);
                rel_op = raw_get_op(raw_rel_val);
            }
        }
    }
    *set = m1;
    *rel = m2;
    return 1;
}


//TODO
TASK_IMPL_2(MDD, dddmc_union, MDD, a, MDD, b)
{
    /* Terminal cases */
    if (a == b) return a;
    if (a == dddmc_false) return b;
    if (b == dddmc_false) return a;
    assert(a != dddmc_true && b != dddmc_true); // expecting same length

    /* Test gc */
    sylvan_gc_test();

    sylvan_stats_count(LDD_UNION);

    /* Improve cache behavior */
    if (a < b) { MDD tmp=b; b=a; a=tmp; }

    /* Access cache */
    MDD result;
    if (cache_get3(CACHE_MDD_UNION, a, b, 0, &result)) {
        sylvan_stats_count(LDD_UNION_CACHED);
        return result;
    }

    /* Get nodes */
    mddnode_t na = GETNODE(a);
    mddnode_t nb = GETNODE(b);

    const int na_copy = dddnode_getcopy(na) ? 1 : 0;
    const int nb_copy = dddnode_getcopy(nb) ? 1 : 0;
    const int32_t na_value = dddnode_getvalue(na);
    const int32_t nb_value = dddnode_getvalue(nb);
    const int8_t na_op = dddnode_getop(na);
    const int8_t nb_op = dddnode_getop(nb);
    const int8_t type = dddnode_gettype(na);

    if(!type){
        /* Perform recursive calculation */
        if (na_copy && nb_copy) {
            dddmc_refs_spawn(SPAWN(dddmc_union, dddnode_getdown(na), dddnode_getdown(nb)));
            MDD right = CALL(dddmc_union, dddnode_getright(na), dddnode_getright(nb));
            dddmc_refs_push(right);
            MDD down = dddmc_refs_sync(SYNC(dddmc_union));
            dddmc_refs_pop(1);
            result = dddmc_make_copynode(down, right);
        } else if (na_copy) {
            MDD right = CALL(dddmc_union, dddnode_getright(na), b);
            result = dddmc_make_copynode(dddnode_getdown(na), right);
        } else if (nb_copy) {
            MDD right = CALL(dddmc_union, a, dddnode_getright(nb));
            result = dddmc_make_copynode(dddnode_getdown(nb), right);
        } else if (na_value < nb_value) {
            MDD right = CALL(dddmc_union, dddnode_getright(na), b);
            result = dddmc_makenode(na_value, dddnode_getdown(na), right, type, na_op);
        } else if (na_value == nb_value) {
            dddmc_refs_spawn(SPAWN(dddmc_union, dddnode_getdown(na), dddnode_getdown(nb)));
            MDD right = CALL(dddmc_union, dddnode_getright(na), dddnode_getright(nb));
            dddmc_refs_push(right);
            MDD down = dddmc_refs_sync(SYNC(dddmc_union));
            dddmc_refs_pop(1);
            result = dddmc_makenode(na_value, down, right, type, na_op);
        } else /* na_value > nb_value */ {
            MDD right = CALL(dddmc_union, a, dddnode_getright(nb));
            result = dddmc_makenode(nb_value, dddnode_getdown(nb), right, type, na_op);
        }
    } else {
        if(na_value < nb_value) {
            MDD down = CALL(dddmc_union, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_union, dddnode_getright(na), b);
            result = dddmc_makenode(na_value, down, right, type, na_op);
        } else if(nb_value < na_value) {
            MDD down = CALL(dddmc_union, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_union, a, dddnode_getright(nb));
            result = dddmc_makenode(nb_value, down, right, type, nb_op);
        } else if(na_op < nb_op){ //nb_value == na_value
            MDD down = CALL(dddmc_union, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_union, dddnode_getright(na), b);
            result = dddmc_makenode(na_value, down, right, type, na_op);
        } else if(nb_op < na_op){
            MDD down = CALL(dddmc_union, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_union, a, dddnode_getright(nb));
            result = dddmc_makenode(nb_value, down, right, type, nb_op);
        } else { //nb_value == na_value && na_op == nb_op
            MDD down = CALL(dddmc_union, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_union, dddnode_getright(na), dddnode_getright(nb));
            result = dddmc_makenode(na_value, down, right, type, na_op);
        }
    }

    /* Write to cache */
    if (cache_put3(CACHE_MDD_UNION, a, b, 0, result)) sylvan_stats_count(LDD_UNION_CACHEDPUT);

    return result;
}
TASK_IMPL_1(int, dddmc_depth, MDD, a)
{
    if(a == dddmc_false || a == dddmc_true){
        return 0;
    } else {
        return 1 + CALL(dddmc_depth,dddmc_getdown(a));
    }
}

TASK_IMPL_1(MDD, dddmc_complement, MDD, a)
{
    /* Test gc */
    sylvan_gc_test();

    if(a == dddmc_true){
        return dddmc_false;
    }
    if(a == dddmc_false){
        return dddmc_true;
    }

    sylvan_stats_count(LDD_COMPLEMENT);

    /* Access cache */
    MDD result;
    if (cache_get3(CACHE_MDD_COMPLEMENT, a, 0, 0, &result)) {
        sylvan_stats_count(LDD_COMPLEMENT_CACHED);
        return result;
    }
    mddnode_t na = GETNODE(a);
    int32_t na_value = dddnode_getvalue(na);
    int8_t type = dddnode_gettype(na);
    int8_t na_op = dddnode_getop(na);

    MDD right;
    if(dddnode_getright(na) == dddmc_false){
        int depth = CALL(dddmc_depth, a);
        int32_t values[depth];
        for(int i = 0; i < depth; i++){
            values[i] = get_raw(raw_get_value(LE_INFTY),1);
        }
        right = dddmc_cube(values, depth, 0);
    } else {
        right = CALL(dddmc_complement,dddnode_getright(na));
    }
    MDD down = CALL(dddmc_complement,dddnode_getdown(na));
    result = dddmc_makenode(na_value, down, right, type, na_op);

    /* Write to cache */
    if (cache_put3(CACHE_MDD_COMPLEMENT, a, 0, 0, result)) sylvan_stats_count(LDD_COMPLEMENT_CACHEDPUT);

    return result;
}

TASK_IMPL_2(MDD, dddmc_nimp, MDD, a, MDD, b)
{
    /* Terminal cases */
    if (a == dddmc_false) return dddmc_false;
    if (a == dddmc_true) return dddmc_complement(b);
    if (b == dddmc_false) return a;
    if (b == dddmc_true) return dddmc_false;
    if (a == b) return dddmc_false;

    /* Test gc */
    sylvan_gc_test();

//    sylvan_stats_count(LDD_UNION);

    /* Improve cache behavior */
    if (a < b) { MDD tmp=b; b=a; a=tmp; }

    /* Access cache */
    MDD result;
//    if (cache_get3(CACHE_MDD_UNION, a, b, 0, &result)) {
//        sylvan_stats_count(LDD_UNION_CACHED);
//        return result;
//    }

    /* Get nodes */
    mddnode_t na = GETNODE(a);
    mddnode_t nb = GETNODE(b);

    const int32_t na_value = dddnode_getvalue(na);
    const int32_t nb_value = dddnode_getvalue(nb);
    const int8_t na_op = dddnode_getop(na);
    const int8_t nb_op = dddnode_getop(nb);
    const int8_t type = dddnode_gettype(na);
    assert(type);

    if(na_value < nb_value) {
        MDD down = CALL(dddmc_union, dddnode_getdown(na), dddnode_getdown(nb));
        MDD right = CALL(dddmc_union, dddnode_getright(na), b);
        result = dddmc_makenode(na_value, down, right, type, na_op);
    } else if(nb_value < na_value) {
        MDD down = CALL(dddmc_union, dddnode_getdown(na), dddnode_getdown(nb));
        MDD right = CALL(dddmc_union, a, dddnode_getright(nb));
        result = dddmc_makenode(nb_value, down, right, type, nb_op);
    } else if(na_op < nb_op){ //nb_value == na_value
        MDD down = CALL(dddmc_union, dddnode_getdown(na), dddnode_getdown(nb));
        MDD right = CALL(dddmc_union, dddnode_getright(na), b);
        result = dddmc_makenode(na_value, down, right, type, na_op);
    } else if(nb_op < na_op){
        MDD down = CALL(dddmc_union, dddnode_getdown(na), dddnode_getdown(nb));
        MDD right = CALL(dddmc_union, a, dddnode_getright(nb));
        result = dddmc_makenode(nb_value, down, right, type, nb_op);
    } else { //nb_value == na_value && na_op == nb_op
        MDD down = CALL(dddmc_union, dddnode_getdown(na), dddnode_getdown(nb));
        MDD right = CALL(dddmc_union, dddnode_getright(na), dddnode_getright(nb));
        result = dddmc_makenode(na_value, down, right, type, na_op);
    }


//    /* Write to cache */
//    if (cache_put3(CACHE_MDD_UNION, a, b, 0, result)) sylvan_stats_count(LDD_UNION_CACHEDPUT);

    return result;
}

//TODO intersect(a,complement(b))
TASK_IMPL_2(MDD, dddmc_minus, MDD, a, MDD, b)
{
    /* Terminal cases */
    if (a == b) return dddmc_false;
    if (a == dddmc_false) return dddmc_false;
    if (b == dddmc_false) return a;
    assert(b != dddmc_true);
    assert(a != dddmc_true); // Universe is unknown!! // Possibly depth issue?

    /* Test gc */
    sylvan_gc_test();

    sylvan_stats_count(LDD_MINUS);

    /* Access cache */
    MDD result;
    if (cache_get3(CACHE_MDD_MINUS, a, b, 0, &result)) {
        sylvan_stats_count(LDD_MINUS_CACHED);
        return result;
    }

    /* Get nodes */
    mddnode_t na = GETNODE(a);
    mddnode_t nb = GETNODE(b);
    int32_t na_value = dddnode_getvalue(na);
    int32_t nb_value = dddnode_getvalue(nb);
    int8_t type = dddnode_gettype(na);
    int8_t na_op = dddnode_getop(na);
    int8_t nb_op = dddnode_getop(nb);

    /* Perform recursive calculation */
    if(!type){
        if (na_value < nb_value) {
            MDD right = CALL(dddmc_minus, dddnode_getright(na), b);
            result = dddmc_makenode(na_value, dddnode_getdown(na), right, 0, 0);
        } else if (na_value == nb_value) {
            dddmc_refs_spawn(SPAWN(dddmc_minus, dddnode_getright(na), dddnode_getright(nb)));
            MDD down = CALL(dddmc_minus, dddnode_getdown(na), dddnode_getdown(nb));
            dddmc_refs_push(down);
            MDD right = dddmc_refs_sync(SYNC(dddmc_minus));
            dddmc_refs_pop(1);
            result = dddmc_makenode(na_value, down, right, 0, 0);
        } else /* na_value > nb_value */ {
            result = CALL(dddmc_minus, a, dddnode_getright(nb));
        }
    } else {
        if (na_value < nb_value || (na_value == nb_value && na_op < nb_op)) {
            MDD right = CALL(dddmc_minus, dddnode_getright(na), b);
            result = dddmc_makenode(na_value, dddnode_getdown(na), right, type, na_op);
        } else if (na_value == nb_value && na_op == nb_op) {
            dddmc_refs_spawn(SPAWN(dddmc_minus, dddnode_getright(na), dddnode_getright(nb)));
            MDD down = CALL(dddmc_minus, dddnode_getdown(na), dddnode_getdown(nb));
            dddmc_refs_push(down);
            MDD right = dddmc_refs_sync(SYNC(dddmc_minus));
            dddmc_refs_pop(1);
            result = dddmc_makenode(na_value, down, right, type, na_op);
        } else /* na_value > nb_value */ {
            result = CALL(dddmc_minus, a, dddnode_getright(nb));
        }



//        MDD right = CALL(dddmc_complement, b);
//        result = CALL(dddmc_intersect, a, right);

//        result = CALL(dddmc_nimp, result, b);
   }

    /* Write to cache */
    if (cache_put3(CACHE_MDD_MINUS, a, b, 0, result)) sylvan_stats_count(LDD_MINUS_CACHEDPUT);

    return result;
}

///* result: a plus b; res2: b minus a */
//TASK_IMPL_3(MDD, lddmc_zip, MDD, a, MDD, b, MDD*, res2)
//{
//    /* Terminal cases */
//    if (a == b) {
//        *res2 = lddmc_false;
//        return a;
//    }
//    if (a == lddmc_false) {
//        *res2 = b;
//        return b;
//    }
//    if (b == lddmc_false) {
//        *res2 = lddmc_false;
//        return a;
//    }
//
//    assert(a != lddmc_true && b != lddmc_true); // expecting same length
//
//    /* Test gc */
//    sylvan_gc_test();
//
//    /* Maybe not the ideal way */
//    sylvan_stats_count(LDD_ZIP);
//
//    /* Access cache */
//    MDD result;
//    if (cache_get3(CACHE_MDD_UNION, a, b, 0, &result) &&
//        cache_get3(CACHE_MDD_MINUS, b, a, 0, res2)) {
//        sylvan_stats_count(LDD_ZIP);
//        return result;
//    }
//
//    /* Get nodes */
//    mddnode_t na = GETNODE(a);
//    mddnode_t nb = GETNODE(b);
//    uint32_t na_value = mddnode_getvalue(na);
//    uint32_t nb_value = mddnode_getvalue(nb);
//
//    /* Perform recursive calculation */
//    if (na_value < nb_value) {
//        MDD right = CALL(lddmc_zip, mddnode_getright(na), b, res2);
//        result = lddmc_makenode(na_value, mddnode_getdown(na), right);
//    } else if (na_value == nb_value) {
//        MDD down2, right2;
//        lddmc_refs_spawn(SPAWN(lddmc_zip, mddnode_getdown(na), mddnode_getdown(nb), &down2));
//        MDD right = CALL(lddmc_zip, mddnode_getright(na), mddnode_getright(nb), &right2);
//        lddmc_refs_push(right);
//        lddmc_refs_push(right2);
//        MDD down = lddmc_refs_sync(SYNC(lddmc_zip));
//        lddmc_refs_pop(2);
//        result = lddmc_makenode(na_value, down, right);
//        *res2 = lddmc_makenode(na_value, down2, right2);
//    } else /* na_value > nb_value */ {
//        MDD right2;
//        MDD right = CALL(lddmc_zip, a, mddnode_getright(nb), &right2);
//        result = lddmc_makenode(nb_value, mddnode_getdown(nb), right);
//        *res2 = lddmc_makenode(nb_value, mddnode_getdown(nb), right2);
//    }
//
//    /* Write to cache */
//    int c1 = cache_put3(CACHE_MDD_UNION, a, b, 0, result);
//    int c2 = cache_put3(CACHE_MDD_MINUS, b, a, 0, *res2);
//    if (c1 && c2) sylvan_stats_count(LDD_ZIP_CACHEDPUT);
//
//    return result;
//}

TASK_IMPL_2(MDD, dddmc_intersect, MDD, a, MDD, b)
{
//    fprintf(stdout, "a: %d, b: %d\n", a, b);
//    fflush(stdout);
    /* Terminal cases */
    if (a == b) return a;
    if (a == dddmc_false || b == dddmc_false) return dddmc_false;
    assert(a != dddmc_true && b != dddmc_true);

    /* Test gc */
    sylvan_gc_test();

    sylvan_stats_count(LDD_INTERSECT);

    /* Get nodes */
    mddnode_t na = GETNODE(a);
    mddnode_t nb = GETNODE(b);
    int32_t na_value = dddnode_getvalue(na);
    int32_t nb_value = dddnode_getvalue(nb);
    int8_t na_op = dddnode_getop(na);
    int8_t nb_op = dddnode_getop(nb);
    int8_t type = dddnode_gettype(na);
    if(!type){
        /* Skip nodes if possible */
        while (na_value != nb_value) {
            if (na_value < nb_value) {
                a = dddnode_getright(na);
                if (a == dddmc_false) return dddmc_false;
                na = GETNODE(a);
                na_value = dddnode_getvalue(na);
            }
            if (nb_value < na_value) {
                b = dddnode_getright(nb);
                if (b == dddmc_false) return dddmc_false;
                nb = GETNODE(b);
                nb_value = dddnode_getvalue(nb);
            }
        }
    }

    /* Access cache */
    MDD result;
    if (cache_get3(CACHE_MDD_INTERSECT, a, b, 0, &result)) {
        sylvan_stats_count(LDD_INTERSECT_CACHED);
        return result;
    }

    /* Perform recursive calculation */
    if(!type){//LDD node
        dddmc_refs_spawn(SPAWN(dddmc_intersect, dddnode_getright(na), dddnode_getright(nb)));
        MDD down = CALL(dddmc_intersect, dddnode_getdown(na), dddnode_getdown(nb));
        dddmc_refs_push(down);
        MDD right = dddmc_refs_sync(SYNC(dddmc_intersect));
        dddmc_refs_pop(1);
        result = dddmc_makenode(na_value, down, right, 0 ,0);
    } else {//DDD node
        if(na_value < nb_value) {
            MDD down = CALL(dddmc_intersect, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_intersect, dddnode_getright(na), b);
            result = dddmc_makenode(na_value, down, right, type, na_op);
        } else if(nb_value < na_value) {
            MDD down = CALL(dddmc_intersect, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_intersect, a, dddnode_getright(nb));
            result = dddmc_makenode(nb_value, down, right, type, nb_op);
        } else if(na_op < nb_op){ //nb_value == na_value
            MDD down = CALL(dddmc_intersect, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_intersect, dddnode_getright(na), b);
            result = dddmc_makenode(na_value, down, right, type, na_op);
        } else if(nb_op < na_op){
            MDD down = CALL(dddmc_intersect, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_intersect, a, dddnode_getright(nb));
            result = dddmc_makenode(nb_value, down, right, type, nb_op);
        } else { //nb_value == na_value && na_op == nb_op
            MDD down = CALL(dddmc_intersect, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_intersect, dddnode_getright(na), dddnode_getright(nb));
            result = dddmc_makenode(na_value, down, right, type, na_op);
        }
    }

    /* Write to cache */
    if (cache_put3(CACHE_MDD_INTERSECT, a, b, 0, result)) sylvan_stats_count(LDD_INTERSECT_CACHEDPUT);

    return result;
}
//TODO caching
TASK_IMPL_2(MDD, dddmc_biimp, MDD, a, MDD, b)
{
    /* Terminal cases */
    if (a == b) return dddmc_true;
    if (a == dddmc_false && b == dddmc_true) return dddmc_false;
    if (b == dddmc_false && a == dddmc_true) return dddmc_false;

    /* Test gc */
    sylvan_gc_test();

    sylvan_stats_count(LDD_BIIMP);

    /* Improve cache behavior */
    if (a < b) { MDD tmp=b; b=a; a=tmp; }

    /* Access cache */
    MDD result;
    if (cache_get3(CACHE_MDD_BIIMP, a, b, 0, &result)) {
        sylvan_stats_count(LDD_BIIMP_CACHED);
        return result;
    }

    /* Get nodes */
    mddnode_t na = GETNODE(a);
    mddnode_t nb = GETNODE(b);

    const int32_t na_value = dddnode_getvalue(na);
    const int32_t nb_value = dddnode_getvalue(nb);
    const int8_t na_op = dddnode_getop(na);
    const int8_t nb_op = dddnode_getop(nb);
    const int8_t type = dddnode_gettype(na);


    if(!type){
        if(na_value != nb_value){
            result = dddmc_false;
        } else {
            MDD down =  CALL(dddmc_biimp, dddnode_getdown(na),  dddnode_getdown(nb));
            MDD right = CALL(dddmc_biimp, dddnode_getright(na), dddnode_getright(nb));
            result = dddmc_makenode(na_value, down, right, type, na_op);
        }
    } else {
        if(b == dddmc_false){
            MDD down = CALL(dddmc_biimp, dddnode_getdown(na), b);
            MDD right = CALL(dddmc_biimp, dddnode_getright(na), b);
            result = dddmc_makenode(na_value, down, right, type, na_op);
        }
        else if(na_value < nb_value) {
            MDD down = CALL(dddmc_biimp, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_biimp, dddnode_getright(na), b);
            result = dddmc_makenode(na_value, down, right, type, na_op);
        } else if(nb_value < na_value) {
            MDD down = CALL(dddmc_biimp, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_biimp, a, dddnode_getright(nb));
            result = dddmc_makenode(nb_value, down, right, type, nb_op);
        } else if(na_op < nb_op){ //nb_value == na_value
            MDD down = CALL(dddmc_biimp, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_biimp, dddnode_getright(na), b);
            result = dddmc_makenode(na_value, down, right, type, na_op);
        } else if(nb_op < na_op){
            MDD down = CALL(dddmc_biimp, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_biimp, a, dddnode_getright(nb));
            result = dddmc_makenode(nb_value, down, right, type, nb_op);
        } else { //nb_value == na_value && na_op == nb_op
            MDD down = CALL(dddmc_biimp, dddnode_getdown(na), dddnode_getdown(nb));
            MDD right = CALL(dddmc_biimp, dddnode_getright(na), dddnode_getright(nb));
            result = dddmc_makenode(na_value, down, right, type, na_op);
        }
    }
    /* Write to cache */
    if (cache_put3(CACHE_MDD_BIIMP, a, b, 0, result)) sylvan_stats_count(LDD_BIIMP_CACHEDPUT);

    return result;
}

// proj: -1 (rest 0), 0 (no match), 1 (match)
TASK_IMPL_3(MDD, dddmc_match, MDD, a, MDD, b, MDD, proj)
{
    if (a == b) return a;
    if (a == dddmc_false || b == dddmc_false) return dddmc_false;

    mddnode_t p_node = GETNODE(proj);
    int32_t p_val = dddnode_getvalue(p_node);
    if (p_val == (int32_t)-1) return a;

    assert(a != dddmc_true);
    if (p_val == 1) assert(b != dddmc_true);

    /* Test gc */
    sylvan_gc_test();

    /* Skip nodes if possible */
    if (p_val == 1) {
        if (!match_ddds(&a, &b)) return dddmc_false;
    }

    sylvan_stats_count(LDD_MATCH);

    /* Access cache */
    MDD result;
    if (cache_get3(CACHE_MDD_MATCH, a, b, proj, &result)) {
        sylvan_stats_count(LDD_MATCH_CACHED);
        return result;
    }

    /* Perform recursive calculation */
    mddnode_t na = GETNODE(a);
    MDD down;
    if (p_val == 1) {
        mddnode_t nb = GETNODE(b);
        /* right = */ dddmc_refs_spawn(SPAWN(dddmc_match, dddnode_getright(na), dddnode_getright(nb), proj));
        down = CALL(dddmc_match, dddnode_getdown(na), dddnode_getdown(nb), dddnode_getdown(p_node));
    } else {
        /* right = */ dddmc_refs_spawn(SPAWN(dddmc_match, dddnode_getright(na), b, proj));
        down = CALL(dddmc_match, dddnode_getdown(na), b, dddnode_getdown(p_node));
    }
    dddmc_refs_push(down);
    MDD right = dddmc_refs_sync(SYNC(dddmc_match));
    dddmc_refs_pop(1);
    result = dddmc_makenode(dddnode_getvalue(na), down, right, dddnode_gettype(na), dddnode_getop(na));

    /* Write to cache */
    if (cache_put3(CACHE_MDD_MATCH, a, b, proj, result)) sylvan_stats_count(LDD_MATCH_CACHEDPUT);

    return result;
}


//Works only for ddd nodes, not ldd nodes
TASK_IMPL_1(int8_t, dddmc_tautology, MDD, a)
{
    if(a == dddmc_true) return 1;
    if(a == dddmc_false) return 0;
    /* Test gc */
    sylvan_gc_test();

    /* Access cache */
    int8_t result;
    mddnode_t na = GETNODE(a);
    const int32_t na_value = dddnode_getvalue(na);
    const int8_t na_op = dddnode_getop(na);

    MDD right = dddnode_getright(na);
    MDD down = dddnode_getdown(na);

    if(right == dddmc_false){
        result = (get_raw(na_value, na_op) == LE_INFTY);
    } else {
        int8_t res_right = CALL(dddmc_tautology, right);
        int8_t res_down = CALL(dddmc_tautology, down);
        result = res_right && res_down;
    }
    return result;
}

TASK_IMPL_2(int8_t, dddmc_equal, MDD, a, MDD, b)
{
    if(a == b) return 1;
    if((a == dddmc_false && b == dddmc_true) || (a == dddmc_true && b == dddmc_false)) return 0;

    /* Get nodes */
    mddnode_t na = GETNODE(a);
    mddnode_t nb = GETNODE(b);

    const int32_t na_value = dddnode_getvalue(na);
    const int32_t nb_value = dddnode_getvalue(nb);
    const int8_t type = dddnode_gettype(na);

    if(!type){
        if(na_value != nb_value){
            return 0;
        } else if(a == dddmc_false){
            int8_t down = CALL(dddmc_equal, a, dddnode_getdown(nb));
            int8_t right = CALL(dddmc_equal, a, dddnode_getright(nb));
            return (int8_t)(down && right);
        } else if(b == dddmc_false){
            int8_t down = CALL(dddmc_equal, dddnode_getdown(na), b);
            int8_t right = CALL(dddmc_equal, dddnode_getright(na), b);
            return (int8_t)(down && right);
        } else {
            int8_t down = CALL(dddmc_equal, dddnode_getdown(na), dddnode_getdown(nb));
            int8_t right = CALL(dddmc_equal, dddnode_getright(na), dddnode_getright(nb));
            return (int8_t)(down && right);
        }
    } else {
        MDD biimp = CALL(dddmc_biimp, a, b);
        return CALL(dddmc_tautology, biimp);
    }

}

TASK_6(MDD, dddmc_relprod_help, int32_t, val, MDD, set, MDD, rel, MDD, proj, int8_t, type, int8_t, op)
{
    return dddmc_makenode(val, CALL(dddmc_relprod, set, rel, proj), dddmc_false, type, op);
}

// meta: -1 (end; rest not in rel), 0 (not in rel), 1 (read), 2 (write), 3 (only-read), 4 (only-write)
TASK_IMPL_3(MDD, dddmc_relprod, MDD, set, MDD, rel, MDD, meta)
{
    if (set == dddmc_false) return dddmc_false;
    if (rel == dddmc_false) return dddmc_false;

    mddnode_t n_meta = GETNODE(meta);
    int32_t m_val = dddnode_getvalue(n_meta);
    if (m_val == (int32_t)-1) return set;
    if (m_val != 0) assert(set != dddmc_true && rel != dddmc_true);

    /* Skip nodes if possible */
    if (!dddnode_getcopy(GETNODE(rel))) {
        if (m_val == 1 || m_val == 3) {
            if (!match_set_rel_ddds(&set, &rel)) return dddmc_false;
        }
    }

    /* Test gc */
    sylvan_gc_test();

    sylvan_stats_count(LDD_RELPROD);

    /* Access cache */
    MDD result;
    if (cache_get3(CACHE_MDD_RELPROD, set, rel, meta, &result)) {
        sylvan_stats_count(LDD_RELPROD_CACHED);
        return result;
    }

    mddnode_t n_set = GETNODE(set);
    int8_t set_type = dddnode_gettype(n_set);
    mddnode_t n_rel = GETNODE(rel);

    /* Recursive operations */
    if (m_val == 0) { // not in rel
        dddmc_refs_spawn(SPAWN(dddmc_relprod, dddnode_getright(n_set), rel, meta));
        MDD down = CALL(dddmc_relprod, dddnode_getdown(n_set), rel, dddnode_getdown(n_meta));
        dddmc_refs_push(down);
        MDD right = dddmc_refs_sync(SYNC(dddmc_relprod));
        dddmc_refs_pop(1);
        result = dddmc_makenode(dddnode_getvalue(n_set), down, right, 0, 0);
    } else if (m_val == 1) { // read
        // read layer: if not copy, then set&rel are already matched
        dddmc_refs_spawn(SPAWN(dddmc_relprod, set, dddnode_getright(n_rel), meta)); // spawn next read in list

        // for this read, either it is copy ('for all') or it is normal match
        if (dddnode_getcopy(n_rel)) {
            // spawn for every value to copy (set)
            int count = 0;
            for (;;) {
                // stay same level of set (for write)
                dddmc_refs_spawn(SPAWN(dddmc_relprod, set, dddnode_getdown(n_rel), dddnode_getdown(n_meta)));
                count++;
                set = dddnode_getright(n_set);
                if (set == dddmc_false) break;
                n_set = GETNODE(set);
            }

            // sync+union (one by one)
            result = dddmc_false;
            while (count--) {
                dddmc_refs_push(result);
                MDD result2 = dddmc_refs_sync(SYNC(dddmc_relprod));
                dddmc_refs_push(result2);
                result = CALL(dddmc_union, result, result2);
                dddmc_refs_pop(2);
            }
        } else {
            // stay same level of set (for write)
            result = CALL(dddmc_relprod, set, dddnode_getdown(n_rel), dddnode_getdown(n_meta));
        }

        dddmc_refs_push(result);
        MDD result2 = dddmc_refs_sync(SYNC(dddmc_relprod)); // sync next read in list
        dddmc_refs_push(result2);
        result = CALL(dddmc_union, result, result2);
        dddmc_refs_pop(2);
    } else if (m_val == 3) { // only-read
        if (dddnode_getcopy(n_rel)) {
            // copy on read ('for any value')
            // result = union(result_with_copy, result_without_copy)
            dddmc_refs_spawn(SPAWN(dddmc_relprod, set, dddnode_getright(n_rel), meta)); // spawn without_copy

            // spawn for every value to copy (set)
            int count = 0;
            for (;;) {
                dddmc_refs_spawn(SPAWN(dddmc_relprod_help, dddnode_getvalue(n_set), dddnode_getdown(n_set), dddnode_getdown(n_rel), dddnode_getdown(n_meta), dddnode_gettype(n_set), dddnode_getop(n_set)));
                count++;
                set = dddnode_getright(n_set);
                if (set == dddmc_false) break;
                n_set = GETNODE(set);
            }

            // sync+union (one by one)
            result = dddmc_false;
            while (count--) {
                dddmc_refs_push(result);
                MDD result2 = dddmc_refs_sync(SYNC(dddmc_relprod_help));
                dddmc_refs_push(result2);
                result = CALL(dddmc_union, result, result2);
                dddmc_refs_pop(2);
            }

            // add result from without_copy
            dddmc_refs_push(result);
            MDD result2 = dddmc_refs_sync(SYNC(lddmc_relprod));
            dddmc_refs_push(result2);
            result = CALL(dddmc_union, result, result2);
            dddmc_refs_pop(2);
        } else {
            // only-read, without copy
            dddmc_refs_spawn(SPAWN(dddmc_relprod, dddnode_getright(n_set), dddnode_getright(n_rel), meta));
            MDD down = CALL(dddmc_relprod, dddnode_getdown(n_set), dddnode_getdown(n_rel), dddnode_getdown(n_meta));
            dddmc_refs_push(down);
            MDD right = dddmc_refs_sync(SYNC(dddmc_relprod));
            dddmc_refs_pop(1);
            result = dddmc_makenode(dddnode_getvalue(n_set), down, right, 0, 0);
        }
    } else if (m_val == 2 || m_val == 4) { // write, only-write
        if (m_val == 4) {
            // only-write, so we need to include 'for all variables'
            dddmc_refs_spawn(SPAWN(dddmc_relprod, dddnode_getright(n_set), rel, meta)); // next in set
        }

        // spawn for every value to write (rel)
        int count = 0;
        for (;;) {
            int32_t value;
            int8_t op = 0;
            if (dddnode_getcopy(n_rel)){
                value = dddnode_getvalue(n_set);
            } if (set_type){
                int32_t raw_value = dddnode_getvalue(n_rel);
                value = raw_get_value(raw_value);
                op = raw_get_op(raw_value);
            } else {
                value = dddnode_getvalue(n_rel);
            }
            dddmc_refs_spawn(SPAWN(dddmc_relprod_help, value, dddnode_getdown(n_set), dddnode_getdown(n_rel), dddnode_getdown(n_meta), set_type, op));
            count++;
            rel = dddnode_getright(n_rel);
            if (rel == dddmc_false) break;
            n_rel = GETNODE(rel);
        }

        // sync+union (one by one)
        result = dddmc_false;
        while (count--) {
            dddmc_refs_push(result);
            MDD result2 = dddmc_refs_sync(SYNC(dddmc_relprod_help));
            dddmc_refs_push(result2);
            result = CALL(dddmc_union, result, result2);
            dddmc_refs_pop(2);
        }

        if (m_val == 4) {
            // sync+union with other variables
            dddmc_refs_push(result);
            MDD result2 = dddmc_refs_sync(SYNC(dddmc_relprod));
            dddmc_refs_push(result2);
            result = CALL(dddmc_union, result, result2);
            dddmc_refs_pop(2);
        }
    }

    /* Write to cache */
    if (cache_put3(CACHE_MDD_RELPROD, set, rel, meta, result)) sylvan_stats_count(LDD_RELPROD_CACHEDPUT);

    return result;
}

//TASK_5(MDD, lddmc_relprod_union_help, uint32_t, val, MDD, set, MDD, rel, MDD, proj, MDD, un)
//{
//    return lddmc_makenode(val, CALL(lddmc_relprod_union, set, rel, proj, un), lddmc_false);
//}
//
//// meta: -1 (end; rest not in rel), 0 (not in rel), 1 (read), 2 (write), 3 (only-read), 4 (only-write)
//TASK_IMPL_4(MDD, lddmc_relprod_union, MDD, set, MDD, rel, MDD, meta, MDD, un)
//{
//    if (set == lddmc_false) return un;
//    if (rel == lddmc_false) return un;
//    if (un == lddmc_false) return CALL(lddmc_relprod, set, rel, meta);
//
//    mddnode_t n_meta = GETNODE(meta);
//    uint32_t m_val = mddnode_getvalue(n_meta);
//    if (m_val == (uint32_t)-1) return CALL(lddmc_union, set, un);
//
//    // check depths (this triggers on logic error)
//    if (m_val != 0) assert(set != lddmc_true && rel != lddmc_true && un != lddmc_true);
//
//    /* Skip nodes if possible */
//    if (!mddnode_getcopy(GETNODE(rel))) {
//        if (m_val == 1 || m_val == 3) {
//            if (!match_ldds(&set, &rel)) return un;
//        }
//    }
//
//    mddnode_t n_set = GETNODE(set);
//    mddnode_t n_rel = GETNODE(rel);
//    mddnode_t n_un = GETNODE(un);
//
//    // in some cases, we know un.value < result.value
//    if (m_val == 0 || m_val == 3) {
//        // if m_val == 0, no read/write, then un.value < set.value?
//        // if m_val == 3, only read (write same), then un.value < set.value?
//        uint32_t set_value = mddnode_getvalue(n_set);
//        uint32_t un_value = mddnode_getvalue(n_un);
//        if (un_value < set_value) {
//            MDD right = CALL(lddmc_relprod_union, set, rel, meta, mddnode_getright(n_un));
//            if (right == mddnode_getright(n_un)) return un;
//            else return lddmc_makenode(mddnode_getvalue(n_un), mddnode_getdown(n_un), right);
//        }
//    } else if (m_val == 2 || m_val == 4) {
//        // if we write, then we only know for certain that un.value < result.value if
//        // the root of rel is not a copy node
//        if (!mddnode_getcopy(n_rel)) {
//            uint32_t rel_value = mddnode_getvalue(n_rel);
//            uint32_t un_value = mddnode_getvalue(n_un);
//            if (un_value < rel_value) {
//                MDD right = CALL(lddmc_relprod_union, set, rel, meta, mddnode_getright(n_un));
//                if (right == mddnode_getright(n_un)) return un;
//                else return lddmc_makenode(mddnode_getvalue(n_un), mddnode_getdown(n_un), right);
//            }
//        }
//    }
//
//    /* Test gc */
//    sylvan_gc_test();
//
//    sylvan_stats_count(LDD_RELPROD_UNION);
//
//    /* Access cache */
//    MDD result;
//    if (cache_get4(CACHE_MDD_RELPROD, set, rel, meta, un, &result)) {
//        sylvan_stats_count(LDD_RELPROD_UNION_CACHED);
//        return result;
//    }
//
//    /* Recursive operations */
//    if (m_val == 0) { // not in rel
//        uint32_t set_value = mddnode_getvalue(n_set);
//        uint32_t un_value = mddnode_getvalue(n_un);
//        // set_value > un_value already checked above
//        if (set_value < un_value) {
//            lddmc_refs_spawn(SPAWN(lddmc_relprod_union, mddnode_getright(n_set), rel, meta, un));
//            // going down, we don't need _union, since un does not contain this subtree
//            MDD down = CALL(lddmc_relprod, mddnode_getdown(n_set), rel, mddnode_getdown(n_meta));
//            lddmc_refs_push(down);
//            MDD right = lddmc_refs_sync(SYNC(lddmc_relprod_union));
//            lddmc_refs_pop(1);
//            if (down == lddmc_false) result = right;
//            else result = lddmc_makenode(mddnode_getvalue(n_set), down, right);
//        } else /* set_value == un_value */ {
//            lddmc_refs_spawn(SPAWN(lddmc_relprod_union, mddnode_getright(n_set), rel, meta, mddnode_getright(n_un)));
//            MDD down = CALL(lddmc_relprod_union, mddnode_getdown(n_set), rel, mddnode_getdown(n_meta), mddnode_getdown(n_un));
//            lddmc_refs_push(down);
//            MDD right = lddmc_refs_sync(SYNC(lddmc_relprod_union));
//            lddmc_refs_pop(1);
//            if (right == mddnode_getright(n_un) && down == mddnode_getdown(n_un)) result = un;
//            else result = lddmc_makenode(mddnode_getvalue(n_set), down, right);
//        }
//    } else if (m_val == 1) { // read
//        // read layer: if not copy, then set&rel are already matched
//        lddmc_refs_spawn(SPAWN(lddmc_relprod_union, set, mddnode_getright(n_rel), meta, un)); // spawn next read in list
//
//        // for this read, either it is copy ('for all') or it is normal match
//        if (mddnode_getcopy(n_rel)) {
//            // spawn for every value in set (copy = for all)
//            int count = 0;
//            for (;;) {
//                // stay same level of set and un (for write)
//                lddmc_refs_spawn(SPAWN(lddmc_relprod_union, set, mddnode_getdown(n_rel), mddnode_getdown(n_meta), un));
//                count++;
//                set = mddnode_getright(n_set);
//                if (set == lddmc_false) break;
//                n_set = GETNODE(set);
//            }
//
//            // sync+union (one by one)
//            result = lddmc_false;
//            while (count--) {
//                lddmc_refs_push(result);
//                MDD result2 = lddmc_refs_sync(SYNC(lddmc_relprod_union));
//                lddmc_refs_push(result2);
//                result = CALL(lddmc_union, result, result2);
//                lddmc_refs_pop(2);
//            }
//        } else {
//            // stay same level of set and un (for write)
//            result = CALL(lddmc_relprod_union, set, mddnode_getdown(n_rel), mddnode_getdown(n_meta), un);
//        }
//
//        lddmc_refs_push(result);
//        MDD result2 = lddmc_refs_sync(SYNC(lddmc_relprod_union)); // sync next read in list
//        lddmc_refs_push(result2);
//        result = CALL(lddmc_union, result, result2);
//        lddmc_refs_pop(2);
//    } else if (m_val == 3) { // only-read
//        // un < set already checked above
//        if (mddnode_getcopy(n_rel)) {
//            // copy on read ('for any value')
//            // result = union(result_with_copy, result_without_copy)
//            lddmc_refs_spawn(SPAWN(lddmc_relprod_union, set, mddnode_getright(n_rel), meta, un)); // spawn without_copy
//
//            // spawn for every value to copy (set)
//            int count = 0;
//            result = lddmc_false;
//            for (;;) {
//                uint32_t set_value = mddnode_getvalue(n_set);
//                uint32_t un_value = mddnode_getvalue(n_un);
//                if (un_value < set_value) {
//                    // this is a bit tricky
//                    // the result of this will simply be "un_value, mddnode_getdown(n_un), false" which is intended
//                    lddmc_refs_spawn(SPAWN(lddmc_relprod_union_help, un_value, lddmc_false, lddmc_false, mddnode_getdown(n_meta), mddnode_getdown(n_un)));
//                    count++;
//                    un = mddnode_getright(n_un);
//                    if (un == lddmc_false) {
//                        result = CALL(lddmc_relprod, set, rel, meta);
//                        break;
//                    }
//                    n_un = GETNODE(un);
//                } else if (un_value > set_value) {
//                    // tricky again. the result of this is a normal relprod
//                    lddmc_refs_spawn(SPAWN(lddmc_relprod_union_help, set_value, mddnode_getdown(n_set), mddnode_getdown(n_rel), mddnode_getdown(n_meta), lddmc_false));
//                    count++;
//                    set = mddnode_getright(n_set);
//                    if (set == lddmc_false) {
//                        result = un;
//                        break;
//                    }
//                    n_set = GETNODE(set);
//                } else /* un_value == set_value */ {
//                    lddmc_refs_spawn(SPAWN(lddmc_relprod_union_help, set_value, mddnode_getdown(n_set), mddnode_getdown(n_rel), mddnode_getdown(n_meta), mddnode_getdown(n_un)));
//                    count++;
//                    set = mddnode_getright(n_set);
//                    un = mddnode_getright(n_un);
//                    if (set == lddmc_false) {
//                        result = un;
//                        break;
//                    } else if (un == lddmc_false) {
//                        result = CALL(lddmc_relprod, set, rel, meta);
//                        break;
//                    }
//                    n_set = GETNODE(set);
//                    n_un = GETNODE(un);
//                }
//            }
//
//            // sync+union (one by one)
//            while (count--) {
//                lddmc_refs_push(result);
//                MDD result2 = lddmc_refs_sync(SYNC(lddmc_relprod_union_help));
//                lddmc_refs_push(result2);
//                result = CALL(lddmc_union, result, result2);
//                lddmc_refs_pop(2);
//            }
//
//            // add result from without_copy
//            lddmc_refs_push(result);
//            MDD result2 = lddmc_refs_sync(SYNC(lddmc_relprod_union));
//            lddmc_refs_push(result2);
//            result = CALL(lddmc_union, result, result2);
//            lddmc_refs_pop(2);
//        } else {
//            // only-read, not a copy node
//            uint32_t set_value = mddnode_getvalue(n_set);
//            uint32_t un_value = mddnode_getvalue(n_un);
//
//            // already did un_value < set_value
//            if (un_value > set_value) {
//                lddmc_refs_spawn(SPAWN(lddmc_relprod_union, mddnode_getright(n_set), mddnode_getright(n_rel), meta, un));
//                MDD down = CALL(lddmc_relprod, mddnode_getdown(n_set), mddnode_getdown(n_rel), mddnode_getdown(n_meta));
//                lddmc_refs_push(down);
//                MDD right = lddmc_refs_sync(SYNC(lddmc_relprod_union));
//                lddmc_refs_pop(1);
//                result = lddmc_makenode(mddnode_getvalue(n_set), down, right);
//            } else /* un_value == set_value */ {
//                lddmc_refs_spawn(SPAWN(lddmc_relprod_union, mddnode_getright(n_set), mddnode_getright(n_rel), meta, mddnode_getright(n_un)));
//                MDD down = CALL(lddmc_relprod_union, mddnode_getdown(n_set), mddnode_getdown(n_rel), mddnode_getdown(n_meta), mddnode_getdown(n_un));
//                lddmc_refs_push(down);
//                MDD right = lddmc_refs_sync(SYNC(lddmc_relprod_union));
//                lddmc_refs_pop(1);
//                result = lddmc_makenode(mddnode_getvalue(n_set), down, right);
//            }
//        }
//    } else if (m_val == 2 || m_val == 4) { // write, only-write
//        if (m_val == 4) {
//            // only-write, so we need to include 'for all variables'
//            lddmc_refs_spawn(SPAWN(lddmc_relprod_union, mddnode_getright(n_set), rel, meta, un)); // next in set
//        }
//
//        // spawn for every value to write (rel)
//        int count = 0;
//        for (;;) {
//            uint32_t value;
//            if (mddnode_getcopy(n_rel)) value = mddnode_getvalue(n_set);
//            else value = mddnode_getvalue(n_rel);
//            uint32_t un_value = mddnode_getvalue(n_un);
//            if (un_value < value) {
//                // the result of this will simply be "un_value, mddnode_getdown(n_un), false" which is intended
//                lddmc_refs_spawn(SPAWN(lddmc_relprod_union_help, un_value, lddmc_false, lddmc_false, mddnode_getdown(n_meta), mddnode_getdown(n_un)));
//                count++;
//                un = mddnode_getright(n_un);
//                if (un == lddmc_false) {
//                    result = CALL(lddmc_relprod, set, rel, meta);
//                    break;
//                }
//                n_un = GETNODE(un);
//            } else if (un_value > value) {
//                lddmc_refs_spawn(SPAWN(lddmc_relprod_union_help, value, mddnode_getdown(n_set), mddnode_getdown(n_rel), mddnode_getdown(n_meta), lddmc_false));
//                count++;
//                rel = mddnode_getright(n_rel);
//                if (rel == lddmc_false) {
//                    result = un;
//                    break;
//                }
//                n_rel = GETNODE(rel);
//            } else /* un_value == value */ {
//                lddmc_refs_spawn(SPAWN(lddmc_relprod_union_help, value, mddnode_getdown(n_set), mddnode_getdown(n_rel), mddnode_getdown(n_meta), mddnode_getdown(n_un)));
//                count++;
//                rel = mddnode_getright(n_rel);
//                un = mddnode_getright(n_un);
//                if (rel == lddmc_false) {
//                    result = un;
//                    break;
//                } else if (un == lddmc_false) {
//                    result = CALL(lddmc_relprod, set, rel, meta);
//                    break;
//                }
//                n_rel = GETNODE(rel);
//                n_un = GETNODE(un);
//            }
//        }
//
//        // sync+union (one by one)
//        while (count--) {
//            lddmc_refs_push(result);
//            MDD result2 = lddmc_refs_sync(SYNC(lddmc_relprod_union_help));
//            lddmc_refs_push(result2);
//            result = CALL(lddmc_union, result, result2);
//            lddmc_refs_pop(2);
//        }
//
//        if (m_val == 4) {
//            // sync+union with other variables
//            lddmc_refs_push(result);
//            MDD result2 = lddmc_refs_sync(SYNC(lddmc_relprod_union));
//            lddmc_refs_push(result2);
//            result = CALL(lddmc_union, result, result2);
//            lddmc_refs_pop(2);
//        }
//    }
//
//    /* Write to cache */
//    if (cache_put4(CACHE_MDD_RELPROD, set, rel, meta, un, result)) sylvan_stats_count(LDD_RELPROD_UNION_CACHEDPUT);
//
//    return result;
//}
//
//TASK_7(MDD, dddmc_relprev_help, int32_t, val, MDD, set, MDD, rel, MDD, proj, MDD, uni, int8_t, type, int8_t op)
//MDD dddmc_relprev_help(int32_t val, MDD set, MDD rel, MDD proj, MDD uni, int8_t type, int8_t op)
TASK_6(MDD, dddmc_relprev_help, int32_t, val, MDD, set, MDD, rel, MDD, proj, MDD, uni, int8_t*, type_op)
{
    return dddmc_makenode(val, CALL(lddmc_relprev, set, rel, proj, uni), lddmc_false, type_op[0], type_op[1]);
}

/**
 * Calculate all predecessors to a in uni according to rel[meta]
 * <meta> follows the same semantics as relprod
 * i.e. 0 (not in rel), 1 (read), 2 (write), 3 (only-read), 4 (only-write), -1 (end; rest=0)
 */
TASK_IMPL_4(MDD, dddmc_relprev, MDD, set, MDD, rel, MDD, meta, MDD, uni)
{
    if (set == dddmc_false) return dddmc_false;
    if (rel == dddmc_false) return dddmc_false;
    if (uni == dddmc_false) return dddmc_false;

    mddnode_t n_meta = GETNODE(meta);
    int32_t m_val = dddnode_getvalue(n_meta);
    if (m_val == (int32_t)-1) {
        if (dddmc_equal(set, uni)) return set;
        else return dddmc_intersect(set, uni);
    }

    if (m_val != 0) assert(set != dddmc_true && rel != dddmc_true && uni != dddmc_true);

    /* Skip nodes if possible */
    if (m_val == 0) {
        // not in rel: match set and uni ('intersect')
        if (!match_ddds(&set, &uni)) return dddmc_false;
    } else if (dddnode_getcopy(GETNODE(rel))) {
        // read+copy: no matching (pre is everything in uni)
        // write+copy: no matching (match after split: set and uni)
        // only-read+copy: match set and uni
        // only-write+copy: no matching (match after split: set and uni)
        if (m_val == 3) {
            if (!match_ddds(&set, &uni)) return dddmc_false;
        }
    } else if (m_val == 1) {
        // read: match uni and rel
        if (!match_ddds(&uni, &rel)) return dddmc_false;
    } else if (m_val == 2) {
        // write: match set and rel
        if (!match_ddds(&set, &rel)) return dddmc_false;
    } else if (m_val == 3) {
        // only-read: match uni and set and rel
        mddnode_t n_set = GETNODE(set);
        mddnode_t n_rel = GETNODE(rel);
        mddnode_t n_uni = GETNODE(uni);
        int8_t set_type = dddnode_gettype(n_set);
        int32_t n_set_value = dddnode_getvalue(n_set);
        int32_t n_rel_value = dddnode_getvalue(n_rel);
        int32_t n_uni_value = dddnode_getvalue(n_uni);
        if(!set_type){
            while (n_uni_value != n_rel_value || n_rel_value != n_set_value) {
                if (n_uni_value < n_rel_value || n_uni_value < n_set_value) {
                    uni = dddnode_getright(n_uni);
                    if (uni == dddmc_false) return dddmc_false;
                    n_uni = GETNODE(uni);
                    n_uni_value = dddnode_getvalue(n_uni);
                }
                if (n_set_value < n_rel_value || n_set_value < n_uni_value) {
                    set = dddnode_getright(n_set);
                    if (set == dddmc_false) return dddmc_false;
                    n_set = GETNODE(set);
                    n_set_value = dddnode_getvalue(n_set);
                }
                if (n_rel_value < n_set_value || n_rel_value < n_uni_value) {
                    rel = dddnode_getright(n_rel);
                    if (rel == dddmc_false) return dddmc_false;
                    n_rel = GETNODE(rel);
                    n_rel_value = dddnode_getvalue(n_rel);
                }
            }
        } else {
            int8_t n_set_op = dddnode_getop(n_set);
            int8_t n_uni_op = dddnode_getop(n_set);
            int8_t n_rel_op = raw_get_op(n_rel_value);
            n_rel_value = raw_get_value(n_rel_value);
            while ((n_uni_value != n_rel_value && n_uni_op != n_rel_op) || (n_rel_value != n_set_value && n_rel_op != n_set_op)) {
                if (n_uni_value < n_rel_value || n_uni_value < n_set_value || (n_uni_value == n_rel_value && n_uni_op < n_rel_op) || (n_uni_value == n_set_value && n_uni_op == n_set_op)) {
                    uni = dddnode_getright(n_uni);
                    if (uni == dddmc_false) return dddmc_false;
                    n_uni = GETNODE(uni);
                    n_uni_value = dddnode_getvalue(n_uni);
                    n_uni_op = dddnode_getop(n_uni);
                }
                if (n_set_value < n_rel_value || n_set_value < n_uni_value || (n_set_value == n_rel_value && n_set_op < n_rel_op) || (n_set_value == n_uni_value && n_set_op < n_uni_op)) {
                    set = dddnode_getright(n_set);
                    if (set == dddmc_false) return dddmc_false;
                    n_set = GETNODE(set);
                    n_set_value = dddnode_getvalue(n_set);
                    n_set_op = dddnode_getop(n_set);
                }
                if (n_rel_value < n_set_value || n_rel_value < n_uni_value || (n_rel_value == n_set_value && n_rel_op < n_set_op) || (n_rel_value == n_uni_value && n_rel_op < n_uni_op)) {
                    rel = dddnode_getright(n_rel);
                    if (rel == dddmc_false) return dddmc_false;
                    n_rel = GETNODE(rel);
                    n_rel_value = raw_get_value(dddnode_getvalue(n_rel));
                    n_rel_op = raw_get_op(dddnode_getvalue(n_rel));
                }
            }
        }
    } else if (m_val == 4) {
        // only-write: match set and rel (then use whole universe)
        if (!match_ddds(&set, &rel)) return dddmc_false;
    }

    /* Test gc */
    sylvan_gc_test();

    sylvan_stats_count(LDD_RELPREV);

    /* Access cache */
    MDD result;
    if (cache_get4(CACHE_MDD_RELPREV, set, rel, meta, uni, &result)) {
        sylvan_stats_count(LDD_RELPREV_CACHED);
        return result;
    }

    mddnode_t n_set = GETNODE(set);
    mddnode_t n_rel = GETNODE(rel);
    mddnode_t n_uni = GETNODE(uni);

    /* Recursive operations */
    if (m_val == 0) { // not in rel
        // m_val == 0 : not in rel (intersection set and universe)
        dddmc_refs_spawn(SPAWN(dddmc_relprev, dddnode_getright(n_set), rel, meta, dddnode_getright(n_uni)));
        MDD down = CALL(dddmc_relprev, dddnode_getdown(n_set), rel, dddnode_getdown(n_meta), dddnode_getdown(n_uni));
        dddmc_refs_push(down);
        MDD right = dddmc_refs_sync(SYNC(dddmc_relprev));
        dddmc_refs_pop(1);
        result = dddmc_makenode(dddnode_getvalue(n_set), down, right, dddnode_gettype(n_set), dddnode_getop(n_set));
    } else if (m_val == 1) { // read level
        // result value is in case of copy: everything in uni!
        // result value is in case of not-copy: match uni and rel!
        dddmc_refs_spawn(SPAWN(dddmc_relprev, set, dddnode_getright(n_rel), meta, uni)); // next in rel
        if (dddnode_getcopy(n_rel)) {
            // result is everything in uni
            // spawn for every value to have been read (uni)
            int count = 0;
            for (;;) {
                dddmc_refs_spawn(SPAWN(dddmc_relprev_help, dddnode_getvalue(n_uni), set, dddnode_getdown(n_rel), dddnode_getdown(n_meta), uni, (int8_t[]){dddnode_gettype(n_uni), dddnode_getop(n_uni)}));
                count++;
                uni = dddnode_getright(n_uni);
                if (uni == dddmc_false) break;
                n_uni = GETNODE(uni);
            }

            // sync+union (one by one)
            result = dddmc_false;
            while (count--) {
                dddmc_refs_push(result);
                MDD result2 = dddmc_refs_sync(SYNC(dddmc_relprev_help));
                dddmc_refs_push(result2);
                result = CALL(dddmc_union, result, result2);
                dddmc_refs_pop(2);
            }
        } else {
            // already matched
            MDD down = CALL(dddmc_relprev, set, dddnode_getdown(n_rel), dddnode_getdown(n_meta), uni);
            result = dddmc_makenode(dddnode_getvalue(n_uni), down, dddmc_false, dddnode_gettype(n_uni), dddnode_getop(n_uni));
        }
        dddmc_refs_push(result);
        MDD result2 = dddmc_refs_sync(SYNC(dddmc_relprev));
        dddmc_refs_push(result2);
        result = CALL(dddmc_union, result, result2);
        dddmc_refs_pop(2);
    } else if (m_val == 3) { // only-read level
        // result value is in case of copy: match set and uni! (already done first match)
        // result value is in case of not-copy: match set and uni and rel!
        dddmc_refs_spawn(SPAWN(dddmc_relprev, set, dddnode_getright(n_rel), meta, uni)); // next in rel
        if (dddnode_getcopy(n_rel)) {
            // spawn for every matching set+uni
            int count = 0;
            for (;;) {
                dddmc_refs_spawn(SPAWN(dddmc_relprev_help, dddnode_getvalue(n_uni), dddnode_getdown(n_set), dddnode_getdown(n_rel), dddnode_getdown(n_meta), dddnode_getdown(n_uni), (int8_t[]){dddnode_gettype(n_uni), dddnode_getop(n_uni)}));
                count++;
                uni = dddnode_getright(n_uni);
                if (!match_ddds(&set, &uni)) break;
                n_set = GETNODE(set);
                n_uni = GETNODE(uni);
            }

            // sync+union (one by one)
            result = dddmc_false;
            while (count--) {
                dddmc_refs_push(result);
                MDD result2 = dddmc_refs_sync(SYNC(dddmc_relprev_help));
                dddmc_refs_push(result2);
                result = CALL(dddmc_union, result, result2);
                dddmc_refs_pop(2);
            }
        } else {
            // already matched
            MDD down = CALL(dddmc_relprev, dddnode_getdown(n_set), dddnode_getdown(n_rel), dddnode_getdown(n_meta), dddnode_getdown(n_uni));
            result = dddmc_makenode(dddnode_getvalue(n_uni), down, lddmc_false, dddnode_gettype(n_uni), dddnode_getop(n_uni));
        }
        dddmc_refs_push(result);
        MDD result2 = dddmc_refs_sync(SYNC(dddmc_relprev));
        dddmc_refs_push(result2);
        result = CALL(dddmc_union, result, result2);
        dddmc_refs_pop(2);
    } else if (m_val == 2) { // write level
        // note: the read level has already matched the uni that was read.
        // write+copy: only for the one set equal to uni...
        // write: match set and rel (already done)
        dddmc_refs_spawn(SPAWN(dddmc_relprev, set, dddnode_getright(n_rel), meta, uni));
        if (dddnode_getcopy(n_rel)) {
            MDD down = dddmc_follow(set, dddnode_getvalue(n_uni));
            if (down != dddmc_false) {
                result = CALL(dddmc_relprev, down, dddnode_getdown(n_rel), dddnode_getdown(n_meta), dddnode_getdown(n_uni));
            } else {
                result = dddmc_false;
            }
        } else {
            result = CALL(dddmc_relprev, dddnode_getdown(n_set), dddnode_getdown(n_rel), dddnode_getdown(n_meta), dddnode_getdown(n_uni));
        }
        dddmc_refs_push(result);
        MDD result2 = dddmc_refs_sync(SYNC(dddmc_relprev));
        dddmc_refs_push(result2);
        result = CALL(dddmc_union, result, result2);
        dddmc_refs_pop(2);
    } else if (m_val == 4) { // only-write level
        // only-write+copy: match set and uni after spawn
        // only-write: match set and rel (already done)
        dddmc_refs_spawn(SPAWN(dddmc_relprev, set, dddnode_getright(n_rel), meta, uni));
        if (dddnode_getcopy(n_rel)) {
            // spawn for every matching set+uni
            int count = 0;
            for (;;) {
                if (!match_ddds(&set, &uni)) break;
                n_set = GETNODE(set);
                n_uni = GETNODE(uni);
                dddmc_refs_spawn(SPAWN(dddmc_relprev_help, dddnode_getvalue(n_uni), dddnode_getdown(n_set), dddnode_getdown(n_rel), dddnode_getdown(n_meta), dddnode_getdown(n_uni), (int8_t[]){dddnode_gettype(n_uni), dddnode_getop(n_uni)}));
                count++;
                uni = dddnode_getright(n_uni);
            }

            // sync+union (one by one)
            result = dddmc_false;
            while (count--) {
                dddmc_refs_push(result);
                MDD result2 = dddmc_refs_sync(SYNC(dddmc_relprev_help));
                dddmc_refs_push(result2);
                result = CALL(dddmc_union, result, result2);
                dddmc_refs_pop(2);
            }
        } else {
            // spawn for every value in universe!!
            int count = 0;
            for (;;) {
                dddmc_refs_spawn(SPAWN(dddmc_relprev_help, dddnode_getvalue(n_uni), dddnode_getdown(n_set), dddnode_getdown(n_rel), dddnode_getdown(n_meta), dddnode_getdown(n_uni), (int8_t[]){dddnode_gettype(n_uni), dddnode_getop(n_uni)}));
                count++;
                uni = dddnode_getright(n_uni);
                if (uni == dddmc_false) break;
                n_uni = GETNODE(uni);
            }

            // sync+union (one by one)
            result = dddmc_false;
            while (count--) {
                dddmc_refs_push(result);
                MDD result2 = dddmc_refs_sync(SYNC(dddmc_relprev_help));
                dddmc_refs_push(result2);
                result = CALL(dddmc_union, result, result2);
                dddmc_refs_pop(2);
            }
        }
        dddmc_refs_push(result);
        MDD result2 = dddmc_refs_sync(SYNC(lddmc_relprev));
        dddmc_refs_push(result2);
        result = CALL(dddmc_union, result, result2);
        dddmc_refs_pop(2);
    }

    /* Write to cache */
    if (cache_put4(CACHE_MDD_RELPREV, set, rel, meta, uni, result)) sylvan_stats_count(LDD_RELPREV_CACHEDPUT);

    return result;
}

//// Same 'proj' as project. So: proj: -2 (end; quantify rest), -1 (end; keep rest), 0 (quantify), 1 (keep)
//TASK_IMPL_4(MDD, lddmc_join, MDD, a, MDD, b, MDD, a_proj, MDD, b_proj)
//{
//    if (a == lddmc_false || b == lddmc_false) return lddmc_false;
//
//    /* Test gc */
//    sylvan_gc_test();
//
//    mddnode_t n_a_proj = GETNODE(a_proj);
//    mddnode_t n_b_proj = GETNODE(b_proj);
//    uint32_t a_proj_val = mddnode_getvalue(n_a_proj);
//    uint32_t b_proj_val = mddnode_getvalue(n_b_proj);
//
//    while (a_proj_val == 0 && b_proj_val == 0) {
//        a_proj = mddnode_getdown(n_a_proj);
//        b_proj = mddnode_getdown(n_b_proj);
//        n_a_proj = GETNODE(a_proj);
//        n_b_proj = GETNODE(b_proj);
//        a_proj_val = mddnode_getvalue(n_a_proj);
//        b_proj_val = mddnode_getvalue(n_b_proj);
//    }
//
//    if (a_proj_val == (uint32_t)-2) return b; // no a left
//    if (b_proj_val == (uint32_t)-2) return a; // no b left
//    if (a_proj_val == (uint32_t)-1 && b_proj_val == (uint32_t)-1) return CALL(lddmc_intersect, a, b);
//
//    // At this point, only proj_val {-1, 0, 1}; max one with -1; max one with 0.
//    const int keep_a = a_proj_val != 0;
//    const int keep_b = b_proj_val != 0;
//
//    if (keep_a && keep_b) {
//        // If both 'keep', then match values
//        if (!match_ldds(&a, &b)) return lddmc_false;
//    }
//
//    sylvan_stats_count(LDD_JOIN);
//
//    /* Access cache */
//    MDD result;
//    if (cache_get4(CACHE_MDD_JOIN, a, b, a_proj, b_proj, &result)) {
//        sylvan_stats_count(LDD_JOIN_CACHED);
//        return result;
//    }
//
//    /* Perform recursive calculation */
//    const mddnode_t na = GETNODE(a);
//    const mddnode_t nb = GETNODE(b);
//    uint32_t val;
//    MDD down;
//
//    // Make copies (for cache)
//    MDD _a_proj = a_proj, _b_proj = b_proj;
//    if (keep_a) {
//        if (keep_b) {
//            val = mddnode_getvalue(nb);
//            lddmc_refs_spawn(SPAWN(lddmc_join, mddnode_getright(na), mddnode_getright(nb), a_proj, b_proj));
//            if (a_proj_val != (uint32_t)-1) a_proj = mddnode_getdown(n_a_proj);
//            if (b_proj_val != (uint32_t)-1) b_proj = mddnode_getdown(n_b_proj);
//            down = CALL(lddmc_join, mddnode_getdown(na), mddnode_getdown(nb), a_proj, b_proj);
//        } else {
//            val = mddnode_getvalue(na);
//            lddmc_refs_spawn(SPAWN(lddmc_join, mddnode_getright(na), b, a_proj, b_proj));
//            if (a_proj_val != (uint32_t)-1) a_proj = mddnode_getdown(n_a_proj);
//            if (b_proj_val != (uint32_t)-1) b_proj = mddnode_getdown(n_b_proj);
//            down = CALL(lddmc_join, mddnode_getdown(na), b, a_proj, b_proj);
//        }
//    } else {
//        val = mddnode_getvalue(nb);
//        lddmc_refs_spawn(SPAWN(lddmc_join, a, mddnode_getright(nb), a_proj, b_proj));
//        if (a_proj_val != (uint32_t)-1) a_proj = mddnode_getdown(n_a_proj);
//        if (b_proj_val != (uint32_t)-1) b_proj = mddnode_getdown(n_b_proj);
//        down = CALL(lddmc_join, a, mddnode_getdown(nb), a_proj, b_proj);
//    }
//
//    lddmc_refs_push(down);
//    MDD right = lddmc_refs_sync(SYNC(lddmc_join));
//    lddmc_refs_pop(1);
//    result = lddmc_makenode(val, down, right);
//
//    /* Write to cache */
//    if (cache_put4(CACHE_MDD_JOIN, a, b, _a_proj, _b_proj, result)) sylvan_stats_count(LDD_JOIN_CACHEDPUT);
//
//    return result;
//}

// so: proj: -2 (end; quantify rest), -1 (end; keep rest), 0 (quantify), 1 (keep)
TASK_IMPL_2(MDD, dddmc_project, const MDD, mdd, const MDD, proj)
{
    if (mdd == dddmc_false) return dddmc_false; // projection of empty is empty
    if (mdd == dddmc_true) return dddmc_true; // projection of universe is universe...

    mddnode_t p_node = GETNODE(proj);
    int32_t p_val = dddnode_getvalue(p_node);
    if (p_val == (int32_t)-1) return mdd;
    if (p_val == (int32_t)-2) return dddmc_true; // because we always end with true.

    sylvan_gc_test();

    sylvan_stats_count(LDD_PROJECT);

    MDD result;
    if (cache_get3(CACHE_MDD_PROJECT, mdd, proj, 0, &result)) {
        sylvan_stats_count(LDD_PROJECT_CACHED);
        return result;
    }

    mddnode_t n = GETNODE(mdd);
    int8_t type = dddnode_gettype(n);
    int8_t op = dddnode_getop(n);
    int32_t value = dddnode_getvalue(n);


    if (p_val == 1) { // keep
        dddmc_refs_spawn(SPAWN(dddmc_project, dddnode_getright(n), proj));
        MDD down = CALL(dddmc_project, dddnode_getdown(n), dddnode_getdown(p_node));
        dddmc_refs_push(down);
        MDD right = dddmc_refs_sync(SYNC(dddmc_project));
        dddmc_refs_pop(1);
        result = dddmc_makenode(value, down, right, type, op);
    } else { // quantify
        if (dddnode_getdown(n) == dddmc_true) { // assume lowest level
            result = dddmc_true;
        } else {
            int count = 0;
            MDD p_down = dddnode_getdown(p_node), _mdd=mdd;
            while (1) {
                dddmc_refs_spawn(SPAWN(dddmc_project, dddnode_getdown(n), p_down));
                count++;
                _mdd = dddnode_getright(n);
                assert(_mdd != dddmc_true);
                if (_mdd == dddmc_false) break;
                n = GETNODE(_mdd);
            }
            result = dddmc_false;
            while (count--) {
                dddmc_refs_push(result);
                MDD down = dddmc_refs_sync(SYNC(dddmc_project));
                dddmc_refs_push(down);
                result = CALL(dddmc_union, result, down);
                dddmc_refs_pop(2);
            }
        }
    }

    if (cache_put3(CACHE_MDD_PROJECT, mdd, proj, 0, result)) sylvan_stats_count(LDD_PROJECT_CACHEDPUT);

    return result;
}

//// so: proj: -2 (end; quantify rest), -1 (end; keep rest), 0 (quantify), 1 (keep)
//TASK_IMPL_3(MDD, lddmc_project_minus, const MDD, mdd, const MDD, proj, MDD, avoid)
//{
//    // This implementation assumed "avoid" has correct depth
//    if (avoid == lddmc_true) return lddmc_false;
//    if (mdd == avoid) return lddmc_false;
//    if (mdd == lddmc_false) return lddmc_false; // projection of empty is empty
//    if (mdd == lddmc_true) return lddmc_true; // avoid != lddmc_true
//
//    mddnode_t p_node = GETNODE(proj);
//    uint32_t p_val = mddnode_getvalue(p_node);
//    if (p_val == (uint32_t)-1) return lddmc_minus(mdd, avoid);
//    if (p_val == (uint32_t)-2) return lddmc_true;
//
//    sylvan_gc_test();
//
//    sylvan_stats_count(LDD_PROJECT_MINUS);
//
//    MDD result;
//    if (cache_get3(CACHE_MDD_PROJECT, mdd, proj, avoid, &result)) {
//        sylvan_stats_count(LDD_PROJECT_MINUS_CACHED);
//        return result;
//    }
//
//    mddnode_t n = GETNODE(mdd);
//
//    if (p_val == 1) { // keep
//        // move 'avoid' until it matches
//        uint32_t val = mddnode_getvalue(n);
//        MDD a_down = lddmc_false;
//        while (avoid != lddmc_false) {
//            mddnode_t a_node = GETNODE(avoid);
//            uint32_t a_val = mddnode_getvalue(a_node);
//            if (a_val > val) {
//                break;
//            } else if (a_val == val) {
//                a_down = mddnode_getdown(a_node);
//                break;
//            }
//            avoid = mddnode_getright(a_node);
//        }
//        lddmc_refs_spawn(SPAWN(lddmc_project_minus, mddnode_getright(n), proj, avoid));
//        MDD down = CALL(lddmc_project_minus, mddnode_getdown(n), mddnode_getdown(p_node), a_down);
//        lddmc_refs_push(down);
//        MDD right = lddmc_refs_sync(SYNC(lddmc_project_minus));
//        lddmc_refs_pop(1);
//        result = lddmc_makenode(val, down, right);
//    } else { // quantify
//        if (mddnode_getdown(n) == lddmc_true) { // assume lowest level
//            result = lddmc_true;
//        } else {
//            int count = 0;
//            MDD p_down = mddnode_getdown(p_node), _mdd=mdd;
//            while (1) {
//                lddmc_refs_spawn(SPAWN(lddmc_project_minus, mddnode_getdown(n), p_down, avoid));
//                count++;
//                _mdd = mddnode_getright(n);
//                assert(_mdd != lddmc_true);
//                if (_mdd == lddmc_false) break;
//                n = GETNODE(_mdd);
//            }
//            result = lddmc_false;
//            while (count--) {
//                lddmc_refs_push(result);
//                MDD down = lddmc_refs_sync(SYNC(lddmc_project_minus));
//                lddmc_refs_push(down);
//                result = CALL(lddmc_union, result, down);
//                lddmc_refs_pop(2);
//            }
//        }
//    }
//
//    if (cache_put3(CACHE_MDD_PROJECT, mdd, proj, avoid, result)) sylvan_stats_count(LDD_PROJECT_MINUS_CACHEDPUT);
//
//    return result;
//}
//TODO

TASK_IMPL_4(MDD, dddmc_union_cube, MDD, a, int32_t*,  values, size_t, count, int, discrete_vars)
{
    if (a == dddmc_false) return dddmc_cube(values, count, discrete_vars);
    if (a == dddmc_true) {
        assert(count == 0);
        return dddmc_true;
    }
    assert(count != 0);

    mddnode_t na = GETNODE(a);
    int32_t na_value = dddnode_getvalue(na);
    int8_t na_type = dddnode_gettype(na);

    /* Only create a new node if something actually changed */
    if(!na_type){//LDD node
        if (na_value < *values) {
            MDD right = dddmc_union_cube(dddnode_getright(na), values, count, discrete_vars);
            if (right == dddnode_getright(na)) return a; // no actual change
            return dddmc_makenode(na_value, dddnode_getdown(na), right,0,0);
        } else if (na_value == *values) {
            MDD down = dddmc_union_cube(dddnode_getdown(na), values+1, count-1, discrete_vars - 1);
            if (down == dddnode_getdown(na)) return a; // no actual change
            return dddmc_makenode(na_value, down, dddnode_getright(na),0,0);
        } else /* na_value > *values */ {
            return dddmc_makenode(*values, dddmc_cube(values+1, count-1, discrete_vars - 1), a,0,0);
        }
    } else {//DDD node
        MDD b = dddmc_cube(values, count, 0);
        MDD result = CALL(dddmc_union,a, b);
        return result;
    }
}
//TODO
MDD
dddmc_union_cube_copy(MDD a, int32_t* values, int* copy, size_t count)
{
    if (a == dddmc_false) return dddmc_cube_copy(values, copy, count);
    if (a == dddmc_true) {
        assert(count == 0);
        return dddmc_true;
    }
    assert(count != 0);

    mddnode_t na = GETNODE(a);

    /* Only create a new node if something actually changed */

    int na_copy = dddnode_getcopy(na);
    if (na_copy && *copy) {
        MDD down = dddmc_union_cube_copy(dddnode_getdown(na), values+1, copy+1, count-1);
        if (down == dddnode_getdown(na)) return a; // no actual change
        return dddmc_make_copynode(down, dddnode_getright(na));
    } else if (na_copy) {
        MDD right = dddmc_union_cube_copy(dddnode_getright(na), values, copy, count);
        if (right == dddnode_getright(na)) return a; // no actual change
        return dddmc_make_copynode(dddnode_getdown(na), right);
    } else if (*copy) {
        return dddmc_make_copynode(dddmc_cube_copy(values+1, copy+1, count-1), a);
    }

    int32_t na_value = dddnode_getvalue(na);
    if (na_value < *values) {
        MDD right = dddmc_union_cube_copy(dddnode_getright(na), values, copy, count);
        if (right == dddnode_getright(na)) return a; // no actual change
        return dddmc_makenode(na_value, dddnode_getdown(na), right,0,0);
    } else if (na_value == *values) {
        MDD down = dddmc_union_cube_copy(dddnode_getdown(na), values+1, copy+1, count-1);
        if (down == dddnode_getdown(na)) return a; // no actual change
        return dddmc_makenode(na_value, down, dddnode_getright(na),0,0);
    } else /* na_value > *values */ {
        return dddmc_makenode(*values, dddmc_cube_copy(values+1, copy+1, count-1), a,0,0);
    }
}

int
dddmc_member_cube(MDD a, int32_t* values, size_t count)
{
    while (1) {
        if (a == dddmc_false) return 0;
        if (a == dddmc_true) return 1;
        assert(count > 0); // size mismatch

        //TODO hier gaat een specifieke DDD follow nodig zijn
        a = dddmc_follow(a, *values);
        values++;
        count--;
    }
}

//int
//lddmc_member_cube_copy(MDD a, uint32_t* values, int* copy, size_t count)
//{
//    while (1) {
//        if (a == lddmc_false) return 0;
//        if (a == lddmc_true) return 1;
//        assert(count > 0); // size mismatch
//
//        if (*copy) a = lddmc_followcopy(a);
//        else a = lddmc_follow(a, *values);
//        values++;
//        count--;
//    }
//}


MDD
dddmc_cube(int32_t* values, size_t count, int discrete_vars)
{
    if (count == 0) return dddmc_true;
    int8_t op = 0;
    int8_t type = 0;
    if (discrete_vars <= 0){
        type = 1;
        op = raw_get_op(*values);
        *values = raw_get_value(*values);
    }
    return dddmc_makenode(*values, dddmc_cube(values+1, count-1, discrete_vars-1), dddmc_false, type, op);
}
//TODO
MDD
dddmc_cube_copy(int32_t* values, int* copy, size_t count)
{
    if (count == 0) return dddmc_true;
    if (*copy) return dddmc_make_copynode(dddmc_cube_copy(values+1, copy+1, count-1), dddmc_false);
    else return dddmc_makenode(*values, dddmc_cube_copy(values+1, copy+1, count-1), dddmc_false,0,0);
}

/**
 * Count number of nodes for each level
 */

//static void
//lddmc_nodecount_levels_mark(MDD mdd, size_t *variables)
//{
//    if (mdd <= lddmc_true) return;
//    mddnode_t n = GETNODE(mdd);
//    if (!mddnode_getmark(n)) {
//        mddnode_setmark(n, 1);
//        (*variables) += 1;
//        lddmc_nodecount_levels_mark(mddnode_getright(n), variables);
//        lddmc_nodecount_levels_mark(mddnode_getdown(n), variables+1);
//    }
//}
//
//static void
//lddmc_nodecount_levels_unmark(MDD mdd)
//{
//    if (mdd <= lddmc_true) return;
//    mddnode_t n = GETNODE(mdd);
//    if (mddnode_getmark(n)) {
//        mddnode_setmark(n, 0);
//        lddmc_nodecount_levels_unmark(mddnode_getright(n));
//        lddmc_nodecount_levels_unmark(mddnode_getdown(n));
//    }
//}
//
//void
//lddmc_nodecount_levels(MDD mdd, size_t *variables)
//{
//    lddmc_nodecount_levels_mark(mdd, variables);
//    lddmc_nodecount_levels_unmark(mdd);
//}

/**
 * Count number of nodes in MDD
 */

static size_t
dddmc_nodecount_mark(MDD mdd)
{
    if (mdd <= dddmc_true) return 0;
    mddnode_t n = GETNODE(mdd);
    if (dddnode_getmark(n)) return 0;
    dddnode_setmark(n, 1);
    return 1 + dddmc_nodecount_mark(dddnode_getdown(n)) + dddmc_nodecount_mark(dddnode_getright(n));
}

static void
dddmc_nodecount_unmark(MDD mdd)
{
    if (mdd <= dddmc_true) return;
    mddnode_t n = GETNODE(mdd);
    if (dddnode_getmark(n)) {
        dddnode_setmark(n, 0);
        dddmc_nodecount_unmark(dddnode_getright(n));
        dddmc_nodecount_unmark(dddnode_getdown(n));
    }
}

size_t
dddmc_nodecount(MDD mdd)
{
    size_t result = dddmc_nodecount_mark(mdd);
    dddmc_nodecount_unmark(mdd);
    return result;
}

/**
 * CALCULATE NUMBER OF VAR ASSIGNMENTS THAT YIELD TRUE
 */

TASK_IMPL_1(dddmc_satcount_double_t, dddmc_satcount_cached, MDD, mdd)
{
    if (mdd == dddmc_false) return 0.0;
    if (mdd == dddmc_true) return 1.0;

    /* Perhaps execute garbage collection */
    sylvan_gc_test();

    union {
        dddmc_satcount_double_t d;
        uint64_t s;
    } hack;

    sylvan_stats_count(LDD_SATCOUNT);

    if (cache_get3(CACHE_MDD_SATCOUNT, mdd, 0, 0, &hack.s)) {
        sylvan_stats_count(LDD_SATCOUNT_CACHED);
        return hack.d;
    }

    mddnode_t n = GETNODE(mdd);
    if(dddnode_gettype(n)) return 1.0;
    SPAWN(dddmc_satcount_cached, dddnode_getdown(n));
    dddmc_satcount_double_t right = CALL(dddmc_satcount_cached, dddnode_getright(n));
    hack.d = right + SYNC(dddmc_satcount_cached);
    if (cache_put3(CACHE_MDD_SATCOUNT, mdd, 0, 0, hack.s)) sylvan_stats_count(LDD_SATCOUNT_CACHEDPUT);

    return hack.d;
}

void dddmc_print_discrete_states(MDD mdd, int discrete_vars, int depth, int* values){
    if (mdd==dddmc_false) return;

    mddnode_t n = GETNODE(mdd);
    int8_t type = dddnode_gettype(n);
    if(type){
        for(int i = 0; i < discrete_vars; i++){
            fprintf(stdout, "%u,", values[i]);
        }
        fprintf(stdout, "\n");
        fflush(stdout);
    } else {
        values[depth] = dddnode_getvalue(n);
        dddmc_print_discrete_states(dddnode_getdown(n), discrete_vars, depth + 1, values);
        dddmc_print_discrete_states(dddnode_getright(n), discrete_vars, depth, values);
    }
    return;
}

TASK_IMPL_1(long double, dddmc_satcount, MDD, mdd)
{
    if (mdd == dddmc_false) return 0.0;
    if (mdd == dddmc_true) return 1.0;

    /* Perhaps execute garbage collection */
    sylvan_gc_test();

    sylvan_stats_count(LDD_SATCOUNTL);

    union {
        long double d;
        struct {
            uint64_t s1;
            uint64_t s2;
        } s;
    } hack;

    if (cache_get3(CACHE_MDD_SATCOUNTL1, mdd, 0, 0, &hack.s.s1) &&
        cache_get3(CACHE_MDD_SATCOUNTL2, mdd, 0, 0, &hack.s.s2)) {
        sylvan_stats_count(LDD_SATCOUNTL_CACHED);
        return hack.d;
    }

    mddnode_t n = GETNODE(mdd);

    SPAWN(dddmc_satcount, dddnode_getdown(n));
    long double right = CALL(dddmc_satcount, dddnode_getright(n));
    hack.d = right + SYNC(dddmc_satcount);

    int c1 = cache_put3(CACHE_MDD_SATCOUNTL1, mdd, 0, 0, hack.s.s1);
    int c2 = cache_put3(CACHE_MDD_SATCOUNTL2, mdd, 0, 0, hack.s.s2);
    if (c1 && c2) sylvan_stats_count(LDD_SATCOUNTL_CACHEDPUT);

    return hack.d;
}

//TASK_IMPL_5(MDD, lddmc_collect, MDD, mdd, lddmc_collect_cb, cb, void*, context, uint32_t*, values, size_t, count)
//{
//    if (mdd == lddmc_false) return lddmc_false;
//    if (mdd == lddmc_true) {
//        return WRAP(cb, values, count, context);
//    }
//
//    mddnode_t n = GETNODE(mdd);
//
//    lddmc_refs_spawn(SPAWN(lddmc_collect, mddnode_getright(n), cb, context, values, count));
//
//    uint32_t newvalues[count+1];
//    if (count > 0) memcpy(newvalues, values, sizeof(uint32_t)*count);
//    newvalues[count] = mddnode_getvalue(n);
//    MDD down = CALL(lddmc_collect, mddnode_getdown(n), cb, context, newvalues, count+1);
//
//    if (down == lddmc_false) {
//        MDD result = lddmc_refs_sync(SYNC(lddmc_collect));
//        return result;
//    }
//
//    lddmc_refs_push(down);
//    MDD right = lddmc_refs_sync(SYNC(lddmc_collect));
//
//    if (right == lddmc_false) {
//        lddmc_refs_pop(1);
//        return down;
//    } else {
//        lddmc_refs_push(right);
//        MDD result = CALL(lddmc_union, down, right);
//        lddmc_refs_pop(2);
//        return result;
//    }
//}
//TODO
VOID_TASK_6(_dddmc_sat_all_nopar, MDD, mdd, dddmc_enum_cb, cb, void*, context, int32_t*, values, size_t, count, size_t, max_count)
{
    if(max_count < count){fprintf(stdout, "max: %zu, count:%zu\n", max_count, count); fflush(stdout);}
    if (mdd == dddmc_false) return;
    if (mdd == dddmc_true) {
        while(count < max_count){
            fprintf(stdout, "max: %zu, count:%zu\n", max_count, count); fflush(stdout);
        }
        WRAP(cb, values, count, context);
        return;
    }

    mddnode_t n = GETNODE(mdd);
    if(dddnode_gettype(n)){
        values[count] = get_raw(dddnode_getvalue(n), dddnode_getop(n));
    } else {
        values[count] = dddnode_getvalue(n);
    }
    CALL(_dddmc_sat_all_nopar, dddnode_getdown(n), cb, context, values, count+1, max_count);
    CALL(_dddmc_sat_all_nopar, dddnode_getright(n), cb, context, values, count, max_count);
}
//TODO
VOID_TASK_IMPL_4(dddmc_sat_all_nopar, MDD, mdd, dddmc_enum_cb, cb, int, count, void*, context)
{
    int32_t values[count];
    CALL(_dddmc_sat_all_nopar, mdd, cb, context, values, 0, count);
}

VOID_TASK_IMPL_5(dddmc_sat_all_par, MDD, mdd, dddmc_enum_cb, cb, void*, context, int32_t*, values, size_t, count)
{
    if (mdd == dddmc_false) return;
    if (mdd == dddmc_true) {
        WRAP(cb, values, count, context);
        return;
    }

    mddnode_t n = GETNODE(mdd);
    int8_t type = dddnode_gettype(n);
    SPAWN(dddmc_sat_all_par, dddnode_getright(n), cb, context, values, count);

    int32_t newvalues[count+1];
    if (count > 0) memcpy(newvalues, values, sizeof(int32_t)*count);
    if(type){
        newvalues[count] = get_raw(dddnode_getvalue(n), dddnode_gettype(n));
    } else {
        newvalues[count] = dddnode_getvalue(n);
    }
    CALL(dddmc_sat_all_par, dddnode_getdown(n), cb, context, newvalues, count+1);

    SYNC(dddmc_sat_all_par);
}
//
//struct lddmc_match_sat_info
//{
//    MDD mdd;
//    MDD match;
//    MDD proj;
//    size_t count;
//    uint32_t values[0];
//};
//
//// proj: -1 (rest 0), 0 (no match), 1 (match)
//VOID_TASK_3(lddmc_match_sat, struct lddmc_match_sat_info *, info, lddmc_enum_cb, cb, void*, context)
//{
//    MDD a = info->mdd, b = info->match, proj = info->proj;
//
//    if (a == lddmc_false || b == lddmc_false) return;
//
//    if (a == lddmc_true) {
//        assert(b == lddmc_true);
//        WRAP(cb, info->values, info->count, context);
//        return;
//    }
//
//    mddnode_t p_node = GETNODE(proj);
//    uint32_t p_val = mddnode_getvalue(p_node);
//    if (p_val == (uint32_t)-1) {
//        assert(b == lddmc_true);
//        CALL(lddmc_sat_all_par, a, cb, context, info->values, info->count);
//        return;
//    }
//
//    /* Get nodes */
//    mddnode_t na = GETNODE(a);
//    mddnode_t nb = GETNODE(b);
//    uint32_t na_value = mddnode_getvalue(na);
//    uint32_t nb_value = mddnode_getvalue(nb);
//
//    /* Skip nodes if possible */
//    if (p_val == 1) {
//        while (na_value != nb_value) {
//            if (na_value < nb_value) {
//                a = mddnode_getright(na);
//                if (a == lddmc_false) return;
//                na = GETNODE(a);
//                na_value = mddnode_getvalue(na);
//            }
//            if (nb_value < na_value) {
//                b = mddnode_getright(nb);
//                if (b == lddmc_false) return;
//                nb = GETNODE(b);
//                nb_value = mddnode_getvalue(nb);
//            }
//        }
//    }
//
//    struct lddmc_match_sat_info *ri = (struct lddmc_match_sat_info*)alloca(sizeof(struct lddmc_match_sat_info)+sizeof(uint32_t[info->count]));
//    struct lddmc_match_sat_info *di = (struct lddmc_match_sat_info*)alloca(sizeof(struct lddmc_match_sat_info)+sizeof(uint32_t[info->count+1]));
//
//    ri->mdd = mddnode_getright(na);
//    di->mdd = mddnode_getdown(na);
//    ri->match = b;
//    di->match = mddnode_getdown(nb);
//    ri->proj = proj;
//    di->proj = mddnode_getdown(p_node);
//    ri->count = info->count;
//    di->count = info->count+1;
//    if (ri->count > 0) memcpy(ri->values, info->values, sizeof(uint32_t[info->count]));
//    if (di->count > 0) memcpy(di->values, info->values, sizeof(uint32_t[info->count]));
//    di->values[info->count] = na_value;
//
//    SPAWN(lddmc_match_sat, ri, cb, context);
//    CALL(lddmc_match_sat, di, cb, context);
//    SYNC(lddmc_match_sat);
//}
//
//VOID_TASK_IMPL_5(lddmc_match_sat_par, MDD, mdd, MDD, match, MDD, proj, lddmc_enum_cb, cb, void*, context)
//{
//    struct lddmc_match_sat_info i;
//    i.mdd = mdd;
//    i.match = match;
//    i.proj = proj;
//    i.count = 0;
//    CALL(lddmc_match_sat, &i, cb, context);
//}
//
int
dddmc_sat_one(MDD mdd, int32_t* values, size_t count)
{
    if (mdd == dddmc_false) return 0;
    if (mdd == dddmc_true) return 1;
    assert(count != 0);
    mddnode_t n = GETNODE(mdd);
    int8_t type = dddnode_gettype(n);
    if(type){
        get_raw(dddnode_getvalue(n), dddnode_getop(n));
    } else {
        *values = dddnode_getvalue(n);
    }
    return dddmc_sat_one(dddnode_getdown(n), values+1, count-1);
}
//
//MDD
//lddmc_sat_one_mdd(MDD mdd)
//{
//    if (mdd == lddmc_false) return lddmc_false;
//    if (mdd == lddmc_true) return lddmc_true;
//    mddnode_t n = GETNODE(mdd);
//    MDD down = lddmc_sat_one_mdd(mddnode_getdown(n));
//    return lddmc_makenode(mddnode_getvalue(n), down, lddmc_false);
//}
//
//TASK_IMPL_4(MDD, lddmc_compose, MDD, mdd, lddmc_compose_cb, cb, void*, context, int, depth)
//{
//    if (depth == 0 || mdd == lddmc_false || mdd == lddmc_true) {
//        return WRAP(cb, mdd, context);
//    } else {
//        mddnode_t n = GETNODE(mdd);
//        lddmc_refs_spawn(SPAWN(lddmc_compose, mddnode_getright(n), cb, context, depth));
//        MDD down = lddmc_compose(mddnode_getdown(n), cb, context, depth-1);
//        lddmc_refs_push(down);
//        MDD right = lddmc_refs_sync(SYNC(lddmc_compose));
//        lddmc_refs_pop(1);
//        return lddmc_makenode(mddnode_getvalue(n), down, right);
//    }
//}
//
//VOID_TASK_IMPL_4(lddmc_visit_seq, MDD, mdd, lddmc_visit_callbacks_t*, cbs, size_t, ctx_size, void*, context)
//{
//    if (WRAP(cbs->lddmc_visit_pre, mdd, context) == 0) return;
//
//    void* context_down = alloca(ctx_size);
//    void* context_right = alloca(ctx_size);
//    WRAP(cbs->lddmc_visit_init_context, context_down, context, 1);
//    WRAP(cbs->lddmc_visit_init_context, context_right, context, 0);
//
//    CALL(lddmc_visit_seq, mddnode_getdown(GETNODE(mdd)), cbs, ctx_size, context_down);
//    CALL(lddmc_visit_seq, mddnode_getright(GETNODE(mdd)), cbs, ctx_size, context_right);
//
//    WRAP(cbs->lddmc_visit_post, mdd, context);
//}
//
//VOID_TASK_IMPL_4(lddmc_visit_par, MDD, mdd, lddmc_visit_callbacks_t*, cbs, size_t, ctx_size, void*, context)
//{
//    if (WRAP(cbs->lddmc_visit_pre, mdd, context) == 0) return;
//
//    void* context_down = alloca(ctx_size);
//    void* context_right = alloca(ctx_size);
//    WRAP(cbs->lddmc_visit_init_context, context_down, context, 1);
//    WRAP(cbs->lddmc_visit_init_context, context_right, context, 0);
//
//    SPAWN(lddmc_visit_par, mddnode_getdown(GETNODE(mdd)), cbs, ctx_size, context_down);
//    CALL(lddmc_visit_par, mddnode_getright(GETNODE(mdd)), cbs, ctx_size, context_right);
//    SYNC(lddmc_visit_par);
//
//    WRAP(cbs->lddmc_visit_post, mdd, context);
//}

/**
 * GENERIC MARK/UNMARK METHODS
 */

static inline int
dddmc_mark(mddnode_t node)
{
    if (dddnode_getmark(node)) return 0;
    dddnode_setmark(node, 1);
    return 1;
}

static inline int
dddmc_unmark(mddnode_t node)
{
    if (dddnode_getmark(node)) {
        dddnode_setmark(node, 0);
        return 1;
    } else {
        return 0;
    }
}

//static void
//lddmc_unmark_rec(mddnode_t node)
//{
//    if (lddmc_unmark(node)) {
//        MDD node_right = mddnode_getright(node);
//        if (node_right > lddmc_true) lddmc_unmark_rec(GETNODE(node_right));
//        MDD node_down = mddnode_getdown(node);
//        if (node_down > lddmc_true) lddmc_unmark_rec(GETNODE(node_down));
//    }
//}

/*************
 * DOT OUTPUT
*************/

static void
dddmc_fprintdot_rec(FILE* out, MDD mdd)
{
    // assert(mdd > lddmc_true);

    // check mark
    mddnode_t n = GETNODE(mdd);
    if (dddnode_getmark(n)) return;
    dddnode_setmark(n, 1);

    // print the node
    int32_t val = dddnode_getvalue(n);
    int8_t type = dddnode_gettype(n);
    int8_t op = dddnode_getop(n);
    fprintf(out, "%" PRIu64 " [shape=record, label=\"", mdd);
    if (dddnode_getcopy(n)) fprintf(out, "<c> *");
    else fprintf(out, "<%d> %d", val, val);
    if(type){
        if(op == 0){
            fprintf(out, "le");
        } else {
            fprintf(out, "leq");
        }
    }
    MDD right = dddnode_getright(n);
    while (right != dddmc_false) {
        mddnode_t n2 = GETNODE(right);
        int32_t val2 = dddnode_getvalue(n2);
        int8_t type2 = dddnode_gettype(n2);
        int8_t op2 = dddnode_getop(n2);
        fprintf(out, "|<%u> %u", val2, val2);
        if(type2){
            if(op2 == 0){
                fprintf(out, "le");
            } else {
                fprintf(out, "leq");
            }
        }
        right = dddnode_getright(n2);
        // assert(right != lddmc_true);
    }
    fprintf(out, "\"];\n");

    // recurse and print the edges
    for (;;) {
        MDD down = dddnode_getdown(n);
        // assert(down != lddmc_false);
        if (down > dddmc_true) {
            dddmc_fprintdot_rec(out, down);
            if (dddnode_getcopy(n)) {
                fprintf(out, "%" PRIu64 ":c -> ", mdd);
            } else {
                fprintf(out, "%" PRIu64 ":%d -> ", mdd, dddnode_getvalue(n));
            }
            if (dddnode_getcopy(GETNODE(down))) {
                fprintf(out, "%" PRIu64 ":c [style=solid];\n", down);
            } else {
                fprintf(out, "%" PRIu64 ":%d [style=solid];\n", down, dddnode_getvalue(GETNODE(down)));
            }
        }
        MDD right = dddnode_getright(n);
        if (right == dddmc_false) break;
        n = GETNODE(right);
    }
}

static void
dddmc_fprintdot_unmark(MDD mdd)
{
    if (mdd <= dddmc_true) return;
    mddnode_t n = GETNODE(mdd);
    if (dddnode_getmark(n)) {
        dddnode_setmark(n, 0);
        for (;;) {
            dddmc_fprintdot_unmark(dddnode_getdown(n));
            mdd = dddnode_getright(n);
            if (mdd == dddmc_false) return;
            n = GETNODE(mdd);
        }
    }
}

void
dddmc_fprintdot(FILE *out, MDD mdd)
{
    fprintf(out, "digraph \"DD\" {\n");
    fprintf(out, "graph [dpi = 300];\n");
    fprintf(out, "center = true;\n");
    fprintf(out, "edge [dir = forward];\n");

    // Special case: false
    if (mdd == dddmc_false) {
        fprintf(out, "0 [shape=record, label=\"False\"];\n");
        fprintf(out, "}\n");
        return;
    }

    // Special case: true
    if (mdd == dddmc_true) {
        fprintf(out, "1 [shape=record, label=\"True\"];\n");
        fprintf(out, "}\n");
        return;
    }

    dddmc_fprintdot_rec(out, mdd);
    dddmc_fprintdot_unmark(mdd);

    fprintf(out, "}\n");
}

//void
//lddmc_printdot(MDD mdd)
//{
//    lddmc_fprintdot(stdout, mdd);
//}

/**
 * Some debug stuff
 */
//void
//lddmc_fprint(FILE *f, MDD mdd)
//{
//    lddmc_serialize_reset();
//    size_t v = lddmc_serialize_add(mdd);
//    fprintf(f, "%zu,", v);
//    lddmc_serialize_totext(f);
//}
//
//void
//lddmc_print(MDD mdd)
//{
//    lddmc_fprint(stdout, mdd);
//}

/**
 * SERIALIZATION
 */

//struct lddmc_ser {
//    MDD mdd;
//    size_t assigned;
//};
//
//// Define a AVL tree type with prefix 'lddmc_ser' holding
//// nodes of struct lddmc_ser with the following compare() function...
//AVL(lddmc_ser, struct lddmc_ser)
//{
//    if (left->mdd > right->mdd) return 1;
//    if (left->mdd < right->mdd) return -1;
//    return 0;
//}
//
//// Define a AVL tree type with prefix 'lddmc_ser_reversed' holding
//// nodes of struct lddmc_ser with the following compare() function...
//AVL(lddmc_ser_reversed, struct lddmc_ser)
//{
//    if (left->assigned > right->assigned) return 1;
//    if (left->assigned < right->assigned) return -1;
//    return 0;
//}
//
//// Initially, both sets are empty
//static avl_node_t *lddmc_ser_set = NULL;
//static avl_node_t *lddmc_ser_reversed_set = NULL;
//
//// Start counting (assigning numbers to MDDs) at 2
//static volatile size_t lddmc_ser_counter = 2;
//static size_t lddmc_ser_done = 0;
//
//// Given a MDD, assign unique numbers to all nodes
//static size_t
//lddmc_serialize_assign_rec(MDD mdd)
//{
//    if (mdd <= lddmc_true) return mdd;
//
//    mddnode_t n = GETNODE(mdd);
//
//    struct lddmc_ser s, *ss;
//    s.mdd = mdd;
//    ss = lddmc_ser_search(lddmc_ser_set, &s);
//    if (ss == NULL) {
//        // assign dummy value
//        s.assigned = 0;
//        ss = lddmc_ser_put(&lddmc_ser_set, &s, NULL);
//
//        // first assign recursively
//        lddmc_serialize_assign_rec(mddnode_getright(n));
//        lddmc_serialize_assign_rec(mddnode_getdown(n));
//
//        // assign real value
//        ss->assigned = lddmc_ser_counter++;
//
//        // put a copy in the reversed table
//        lddmc_ser_reversed_insert(&lddmc_ser_reversed_set, ss);
//    }
//
//    return ss->assigned;
//}
//
//size_t
//lddmc_serialize_add(MDD mdd)
//{
//    return lddmc_serialize_assign_rec(mdd);
//}
//
//void
//lddmc_serialize_reset()
//{
//    lddmc_ser_free(&lddmc_ser_set);
//    lddmc_ser_free(&lddmc_ser_reversed_set);
//    lddmc_ser_counter = 2;
//    lddmc_ser_done = 0;
//}
//
//size_t
//lddmc_serialize_get(MDD mdd)
//{
//    if (mdd <= lddmc_true) return mdd;
//    struct lddmc_ser s, *ss;
//    s.mdd = mdd;
//    ss = lddmc_ser_search(lddmc_ser_set, &s);
//    assert(ss != NULL);
//    return ss->assigned;
//}
//
//MDD
//lddmc_serialize_get_reversed(size_t value)
//{
//    if ((MDD)value <= lddmc_true) return (MDD)value;
//    struct lddmc_ser s, *ss;
//    s.assigned = value;
//    ss = lddmc_ser_reversed_search(lddmc_ser_reversed_set, &s);
//    assert(ss != NULL);
//    return ss->mdd;
//}
//
//void
//lddmc_serialize_totext(FILE *out)
//{
//    avl_iter_t *it = lddmc_ser_reversed_iter(lddmc_ser_reversed_set);
//    struct lddmc_ser *s;
//
//    fprintf(out, "[");
//    while ((s=lddmc_ser_reversed_iter_next(it))) {
//        MDD mdd = s->mdd;
//        mddnode_t n = GETNODE(mdd);
//        fprintf(out, "(%zu,v=%u,d=%zu,r=%zu),", s->assigned,
//                                                mddnode_getvalue(n),
//                                                lddmc_serialize_get(mddnode_getdown(n)),
//                                                lddmc_serialize_get(mddnode_getright(n)));
//    }
//    fprintf(out, "]");
//
//    lddmc_ser_reversed_iter_free(it);
//}
//
//void
//lddmc_serialize_tofile(FILE *out)
//{
//    size_t count = avl_count(lddmc_ser_reversed_set);
//    assert(count >= lddmc_ser_done);
//    assert(count == lddmc_ser_counter-2);
//    count -= lddmc_ser_done;
//    fwrite(&count, sizeof(size_t), 1, out);
//
//    struct lddmc_ser *s;
//    avl_iter_t *it = lddmc_ser_reversed_iter(lddmc_ser_reversed_set);
//
//    /* Skip already written entries */
//    size_t index = 0;
//    while (index < lddmc_ser_done && (s=lddmc_ser_reversed_iter_next(it))) {
//        assert(s->assigned == index+2);
//        index++;
//    }
//
//    while ((s=lddmc_ser_reversed_iter_next(it))) {
//        assert(s->assigned == index+2);
//        index++;
//
//        mddnode_t n = GETNODE(s->mdd);
//
//        struct mddnode node;
//        uint64_t right = lddmc_serialize_get(mddnode_getright(n));
//        uint64_t down = lddmc_serialize_get(mddnode_getdown(n));
//        if (mddnode_getcopy(n)) mddnode_makecopy(&node, right, down);
//        else mddnode_make(&node, mddnode_getvalue(n), right, down);
//
//        assert(right <= index);
//        assert(down <= index);
//
//        fwrite(&node, sizeof(struct mddnode), 1, out);
//    }
//
//    lddmc_ser_done = lddmc_ser_counter-2;
//    lddmc_ser_reversed_iter_free(it);
//}
//
//void
//lddmc_serialize_fromfile(FILE *in)
//{
//    size_t count, i;
//    if (fread(&count, sizeof(size_t), 1, in) != 1) {
//        // TODO FIXME return error
//        printf("sylvan_serialize_fromfile: file format error, giving up\n");
//        exit(-1);
//    }
//
//    for (i=1; i<=count; i++) {
//        struct mddnode node;
//        if (fread(&node, sizeof(struct mddnode), 1, in) != 1) {
//            // TODO FIXME return error
//            printf("sylvan_serialize_fromfile: file format error, giving up\n");
//            exit(-1);
//        }
//
//        assert(mddnode_getright(&node) <= lddmc_ser_done+1);
//        assert(mddnode_getdown(&node) <= lddmc_ser_done+1);
//
//        MDD right = lddmc_serialize_get_reversed(mddnode_getright(&node));
//        MDD down = lddmc_serialize_get_reversed(mddnode_getdown(&node));
//
//        struct lddmc_ser s;
//        if (mddnode_getcopy(&node)) s.mdd = lddmc_make_copynode(down, right);
//        else s.mdd = lddmc_makenode(mddnode_getvalue(&node), down, right);
//        s.assigned = lddmc_ser_done+2; // starts at 0 but we want 2-based...
//        lddmc_ser_done++;
//
//        lddmc_ser_insert(&lddmc_ser_set, &s);
//        lddmc_ser_reversed_insert(&lddmc_ser_reversed_set, &s);
//    }
//}
//
//static void
//lddmc_sha2_rec(MDD mdd, SHA256_CTX *ctx)
//{
//    if (mdd <= lddmc_true) {
//        SHA256_Update(ctx, (void*)&mdd, sizeof(uint64_t));
//        return;
//    }
//
//    mddnode_t node = GETNODE(mdd);
//    if (lddmc_mark(node)) {
//        uint32_t val = mddnode_getvalue(node);
//        SHA256_Update(ctx, (void*)&val, sizeof(uint32_t));
//        lddmc_sha2_rec(mddnode_getdown(node), ctx);
//        lddmc_sha2_rec(mddnode_getright(node), ctx);
//    }
//}
//
//void
//lddmc_printsha(MDD mdd)
//{
//    lddmc_fprintsha(stdout, mdd);
//}
//
//void
//lddmc_fprintsha(FILE *out, MDD mdd)
//{
//    char buf[80];
//    lddmc_getsha(mdd, buf);
//    fprintf(out, "%s", buf);
//}
//
//void
//lddmc_getsha(MDD mdd, char *target)
//{
//    SHA256_CTX ctx;
//    SHA256_Init(&ctx);
//    lddmc_sha2_rec(mdd, &ctx);
//    if (mdd > lddmc_true) lddmc_unmark_rec(GETNODE(mdd));
//    SHA256_End(&ctx, target);
//}
//
//#ifndef NDEBUG
//size_t
//lddmc_test_ismdd(MDD mdd)
//{
//    if (mdd == lddmc_true) return 1;
//    if (mdd == lddmc_false) return 0;
//
//    int first = 1;
//    size_t depth = 0;
//
//    if (mdd != lddmc_false) {
//        mddnode_t n = GETNODE(mdd);
//        if (mddnode_getcopy(n)) {
//            mdd = mddnode_getright(n);
//            depth = lddmc_test_ismdd(mddnode_getdown(n));
//            assert(depth >= 1);
//        }
//    }
//
//    uint32_t value = 0;
//    while (mdd != lddmc_false) {
//        assert(llmsset_is_marked(nodes, mdd));
//
//        mddnode_t n = GETNODE(mdd);
//        uint32_t next_value = mddnode_getvalue(n);
//        assert(mddnode_getcopy(n) == 0);
//        if (first) {
//            first = 0;
//            depth = lddmc_test_ismdd(mddnode_getdown(n));
//            assert(depth >= 1);
//        } else {
//            assert(value < next_value);
//            assert(depth == lddmc_test_ismdd(mddnode_getdown(n)));
//        }
//
//        value = next_value;
//        mdd = mddnode_getright(n);
//    }
//
//    return 1 + depth;
//}
//#endif
