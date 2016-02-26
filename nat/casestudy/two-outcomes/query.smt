; VeriFast free variables.
(assert (forall ((arg6 (_ BitVec 32)))
        (=>  (and
             ;VeriFast collected assumptions
             (bvult #x00000000 arg6)
             (bvule arg6 #x00000400))
                  ;Klee symbolic variables
             (exists ((klee_dmap_value16 (_ BitVec 16))
                      (klee_allocated_index (_ BitVec 32)))
                     (and
                      (bvult #x00000000 klee_allocated_index)
                      (bvule klee_allocated_index #x00000400)
                      (= klee_allocated_index (concat #x0000 klee_dmap_value16))
                      (= klee_allocated_index arg6))))))

(check-sat)
(get-model)
