; VeriFast free variables.
(assert (forall ((t Int) (rez1 Int) (rez2 Int) (rez3 Int) (rez4 Int) (arg1 Int))
                (=> (and
                     ; Assertions collected from the VeriFast path conditions.
                     (not (= rez1 0))
                     (= rez2 0)
                     (<= t rez3)
                     (<= 0 rez4)
                     (not (= rez1 0))
                     (not (not (= rez2 0)))

                     ; Assertions deduced by Klee.
                     (= rez1 1)
                     (= rez2 1)
                     (exists ((next_time Int))
                             (and (= rez3 next_time)
                                  (= next_time arg1))))
                    (exists ((number_of_freed_flows Int))
                            ; The result of the last call in the given call-path segment.
                            (= rez4 number_of_freed_flows)))))
(check-sat)
