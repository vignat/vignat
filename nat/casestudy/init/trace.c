#include <stdint.h>
#include "lib/containers/double-map.h"
#include "lib/containers/double-chain.h"
#include "lib/expirator.h"
#include "lib/my-time.h"
#include "lib/stubs/my-time-stub-control.h"
#include "lib/flow.h"
#include "lib/stubs/loop.h"

void to_verify()
//@ requires true;
//@ ensures true;
{
  struct DoubleMap* arg1;
  struct DoubleChain* arg2;
  start_time();
  /*@ produce_function_pointer_chunk map_keys_equality<int_k>(int_key_eq)(int_k_p)(a, b)
      {
        call();
      }
      @*/
      /*@
      produce_function_pointer_chunk map_keys_equality<ext_k>(ext_key_eq)(ext_k_p)(a, b)
      {
        call();
      }
    @*/
    
  //@ close exists<pair<int_k, ext_k> >(pair(ikc(0,0,0,0,0,0), ekc(0,0,0,0,0,0)));
  //@ close pred_arg4(nat_flow_p);
  int rez1 = dmap_allocate(16, 0, int_key_eq, 16, 16, ext_key_eq, 56, 1024, &arg1);
  // arg1 gets a special value.
  //@ assume(rez1 == 1);
  int rez2 = dchain_allocate(1024, &arg2);
  //@ assume(rez2 == 1);
  // arg2 gets a special value.
  //@ close dmap_dchain_coherent(empty_dmap_fp(), empty_dchain_fp());
  //@ close evproc_loop_invariant(arg1, arg2);
  loop_invariant_consume(&arg1, &arg2);
}
