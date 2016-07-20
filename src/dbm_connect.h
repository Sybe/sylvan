/*
 * dbm_connect.h
 *
 *  Created on: 29 jun. 2016
 *      Author: sybe
 */



#ifdef __cplusplus
extern "C" {
#endif

typedef struct minus_result {
    int count;
    int32_t* dbm_results;
} *minus_result_t;

extern void dbm_minus(int depth, int *a, int *b, int a_count, int b_count, minus_result_t result);

extern void connect_test();

#ifdef __cplusplus
}
#endif
