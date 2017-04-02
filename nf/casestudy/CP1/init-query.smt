; VeriFast free variables.
(assert (forall ((rez1 (_ BitVec 32)) (rez2 (_ BitVec 32)))
        (=>  (and
             ;VeriFast collected assumptions
             (not (= rez1 #x00000000))
                  (= rez1 #x00000001)
                  (not (= rez2 #x00000000))
                  (= rez2 #x00000001)
                  (= rez2 #x00000001))
                  ;Klee symbolic variables
             (exists ((klee_model_version (_ BitVec 32))
                      (klee_dmap_allocation_succeeded (_ BitVec 32))
                      (klee_new_index (_ BitVec 32))
                      (klee_oldest_index (_ BitVec 32))
                      (klee_starting_time (_ BitVec 32))
                      (klee_next_time (_ BitVec 32))
                      (klee_number_of_freed_flows (_ BitVec 32))
                      (klee_queue_num_i (_ BitVec 32))
                      (klee_receive_one (_ BitVec 32)))
                     (and
                      (= #x00000001 rez1)
                      (= #x00000001 rez2)
                      ;Klee collected assumptions
                      (= #x00000001 klee_model_version)
                      (= false
                         (= #x00000001 klee_dmap_allocation_succeeded))
                      (bvsle #x00000001 klee_new_index)
                      (bvslt klee_new_index #x00000400)
                      (bvsle #x00000000 klee_oldest_index)
                      (bvslt klee_oldest_index #x00000400)
                      (bvule klee_starting_time klee_next_time)
                      (bvsle #x00000000 klee_number_of_freed_flows)
                      (bvslt #x00000000 klee_number_of_freed_flows)
                      (bvslt klee_queue_num_i #x00000002)
                      (bvsle #x00000000 klee_queue_num_i)
                      (= #x00000000 klee_receive_one))))))

(check-sat)
(get-model)
