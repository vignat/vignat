(assert (forall ((t Int) (rez1 Int) (rez2 Int) (rez3 Int) (rez4 Int) (arg1 Int))
                (=> (and
                     (not (= rez1 0))
                     (not (= rez2 0))
                     (= rez2 1)
                     (<= t rez3)
                     (<= 0 rez4)
                     (not (= rez1 0))
                     (not (= rez2 0))

                     (= rez1 1)
                     (= rez2 1)
                     (= rez3 arg1)
                     )
                    (exists ((next_time Int) (number_of_freed_flows Int))
                            (and (= rez3 next_time)
                                 (= rez4 number_of_freed_flows))))))
(check-sat)
(get-model)
;\forall t, rez1, rez2, rez3, rez4, arg1

;# VeriFast assumptions

;(not (= rez1 0))
;(not (= rez2 0))
;(= rez2 1)
;(<= t rez3)
;(<= 0 rez4)
;(not (= rez1 0))
;(not (= rez2 0))

;# Klee assumptions
;(= rez1 1)
;(= rez2 1)
;(= rez3 arg1)

;\exists next_time, number_of_freed_flows :

;(= rez3 next_time)
;(= rez4 number_of_freed_flows)
