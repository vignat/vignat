; VeriFast free variables.
(assert (forall ((index_range (_ BitVec 32)) (arg1 (_ BitVec 32))
                 (t (_ BitVec 32))
                 (rez1 (_ BitVec 32)) (rez2 (_ BitVec 32)))
        (=>  (and
             ;VeriFast collected assumptions
              (not (= index_range #x00000400))
              (bvule t rez1)
              (bvsle #x00000000 rez2)
              (= rez1 arg1))
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
                      ;(= klee_next_time rez1)
                      (= klee_number_of_freed_flows rez2)
                      ;(= klee_next_time arg1)
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
                      (or (bvslt #x00000000 klee_number_of_freed_flows)
                          (= #x00000000 klee_number_of_freed_flows))
                      (bvslt klee_queue_num_i #x00000002)
                      (bvsle #x00000000 klee_queue_num_i)
                      (= #x00000000 klee_receive_one))))))

(check-sat)
(get-model)
