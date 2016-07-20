#include <math.h>
#include <stdio.h>
#include "dbm/fed.h"
#include "dbm/ClockAccessor.h"
#include <stdlib.h>
#include <iostream>
#include <dbm_connect.h>


void dbm_minus(int depth, int *a, int *b, int a_count, int b_count, minus_result_t result){

    int clocks = (cindex_t) (sqrt(depth) + 1);
    dbm::fed_t *fed_a;
    fed_a = new dbm::fed_t(clocks);
    for(int i = 0; i < a_count; i++){
        raw_t dbm[clocks*clocks];
        int diagonals = 0;
        for(int j = 0; j < clocks * clocks; j++){
            if(j % (clocks + 1) == 0){
                dbm[j] = 1;
                diagonals++;
            } else {
                dbm[j] = a[i * depth + j - diagonals];
            }
        }
        if(dbm_close(dbm, clocks)){
            fed_a->add(dbm, clocks);
        }
    }
    dbm::fed_t* fed_b;
    fed_b = new dbm::fed_t(clocks);
    for(int i = 0; i < b_count; i++){
        raw_t dbm[clocks*clocks];
        int diagonals = 0;
        for(int j = 0; j < clocks * clocks; j++){
            if(j % (clocks + 1) == 0){
                dbm[j] = 1;
                diagonals++;
            } else {
                dbm[j] = b[i * depth + j - diagonals];
            }
        }
        if(dbm_close(dbm, clocks)){
            fed_b->add(dbm, clocks);
        }
    }
    *fed_a = *fed_a - *fed_b;

    result->count = fed_a->size();

    result->dbm_results = (int32_t*)malloc(fed_a->size() * depth * sizeof(int32_t));
    int zone = 0;
    while(fed_a->size() > 0){
        raw_t *dbm = (raw_t*)malloc(clocks*clocks*sizeof(raw_t));
        fed_a->const_dbmt().copyTo(dbm, clocks);
        int offset = 0;
        for(int i = 0; i < clocks * clocks; i++){
            if(i % (clocks + 1) == 0){
                offset++;
            } else {
                result->dbm_results[zone * depth + i - offset] = (int32_t)(dbm[i]);
            }
        }
//        std::cout << "original on pos: " << zone*depth << ": " << result->dbm_results[zone * depth] << std::endl;
//        fprintf(stdout, "original: %p (%d), %p (%d),%p (%d),%p (%d),%p (%d),%p (%d),%p (%d),%p (%d),%p (%d),%p (%d),%p (%d),%p (%d),\n",
//                (result->dbm_results), *(result->dbm_results),
//                (result->dbm_results +1), *(result->dbm_results +1),
//                (result->dbm_results+2), *(result->dbm_results+2),
//                (result->dbm_results+3),*(result->dbm_results+3),
//                (result->dbm_results+4),*(result->dbm_results+4),
//                (result->dbm_results+5), *(result->dbm_results+5),
//                (result->dbm_results+6),*(result->dbm_results+6),
//                (result->dbm_results+7),*(result->dbm_results+7),
//                (result->dbm_results+8), *(result->dbm_results+8),
//                (result->dbm_results+9), *(result->dbm_results+9),
//                (result->dbm_results+10), *(result->dbm_results+10),
//                (result->dbm_results+11),*(result->dbm_results+11));
                    fflush(stdout);
        fed_a->removeThisDBM(fed_a->const_dbmt());
        zone++;
        assert(fed_a->size() == result->count - zone);
        free(dbm);
    }
}

void connect_test(){
    std::cout << "connect_test succeeded" << std::endl;
    return;
}
