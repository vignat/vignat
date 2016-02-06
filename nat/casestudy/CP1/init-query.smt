; VeriFast free variables.
(assert (forall ((t Int) (rez1 Int) (rez2 Int) (rez3 Int) (rez4 Int) (arg1 Int))
                (=> (and
                     ; Assertions collected from the VeriFast path conditions.
                     (not (= rez1 0))
                     (= rez1 1)
                     (not (= rez2 0))
                     (= rez2 1)
                     (= rez2 1))
                    true)))

(check-sat)
