; VeriFast free variables.
(assert (forall ((t Int) (rez1 Int) (rez2 Int) (arg1 Int))
                (=> (and
                     ; Assertions collected from the VeriFast path conditions.
                     (<= t rez1)
                     (<= 0 rez2)
                     (= rez1 arg1))

                    (exists ((number_of_freed_flows Int))
                            ; The result of the last call in the given call-path segment.
                            (= rez2 number_of_freed_flows)))))
(check-sat)
