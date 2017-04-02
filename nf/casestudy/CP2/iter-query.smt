; VeriFast free variables.
(assert (forall ((t Int) (index_range Int) (i Int)
                 (rez1 Int) (rez2 Int) (rez3 Int) (rez4 Int) (rez5 (_ BitVec 480)) (rez6 Int)
                 (arg1 Int) (arg2 (_ BitVec 128)) (arg3 Int) (arg4 Int) (arg5 Int))
                (=> (and
                     (= index_range 1024)
                     (<= t rez1)
                     (<= 0 rez2)
                     (= rez1 arg1)
                     (<= rez1 rez3)
                     (not (= rez4 0))
                     (<= 0 i)
                     (< i 1024)
                     (= rez4 1)
                     (= arg4 i)
                     (not (= rez5 0))
                     (= arg5 i)
                     (or (= rez6 1) (= rez6 0)));shortcut combining two queries to one.

                    (exists ((user_buf0 (_ BitVec 128)) (queuei (_ BitVec 32)))
                            (= (Concat w128 171
                                       (Concat w120 171
                                               (Concat w112 (Read w8 23 user_buf0)
                                                       (Concat w104
                                                               (Read
                                                                w8
                                                                (Extract
                                                                 w32 0
                                                                 (Add w64 64
                                                                      (Mul w64 64
                                                                           (SExt w64
                                                                                 (ReadLSB
                                                                                  w32
                                                                                  0
                                                                                  queuei))))))
                                                               (Concat w96))))
                            ; The result of the last call in the given call-path segment.
                            (= rez2 number_of_freed_flows)))))
(check-sat)
