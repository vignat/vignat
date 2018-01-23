Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _find_empty : ident := 40%positive.
Definition ___builtin_read32_reversed : ident := 32%positive.
Definition ___compcert_va_int32 : ident := 16%positive.
Definition _index : ident := 38%positive.
Definition _get : ident := 46%positive.
Definition ___builtin_fsqrt : ident := 24%positive.
Definition ___builtin_clz : ident := 22%positive.
Definition ___compcert_va_int64 : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition _size_rec : ident := 50%positive.
Definition _find_key : ident := 43%positive.
Definition ___builtin_va_start : ident := 12%positive.
Definition _value : ident := 47%positive.
Definition ___builtin_annot_intval : ident := 10%positive.
Definition _values : ident := 44%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _start : ident := 36%positive.
Definition ___builtin_read16_reversed : ident := 31%positive.
Definition ___builtin_va_copy : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition ___builtin_fmin : ident := 26%positive.
Definition ___builtin_bswap : ident := 19%positive.
Definition _bb : ident := 39%positive.
Definition ___builtin_membar : ident := 11%positive.
Definition _erase : ident := 49%positive.
Definition _i : ident := 37%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition ___builtin_fmsub : ident := 28%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition _key : ident := 42%positive.
Definition ___builtin_bswap16 : ident := 21%positive.
Definition ___compcert_va_float64 : ident := 18%positive.
Definition ___builtin_annot : ident := 9%positive.
Definition _main : ident := 52%positive.
Definition _val : ident := 45%positive.
Definition _keys : ident := 41%positive.
Definition ___builtin_va_arg : ident := 13%positive.
Definition ___builtin_fmadd : ident := 27%positive.
Definition _k : ident := 33%positive.
Definition ___builtin_fmax : ident := 25%positive.
Definition ___builtin_va_end : ident := 15%positive.
Definition _loop : ident := 34%positive.
Definition ___builtin_fnmadd : ident := 29%positive.
Definition _busybits : ident := 35%positive.
Definition ___builtin_fnmsub : ident := 30%positive.
Definition ___builtin_ctz : ident := 23%positive.
Definition _size : ident := 51%positive.
Definition _put : ident := 48%positive.
Definition ___builtin_bswap32 : ident := 20%positive.
Definition _index'4 : ident := 62%positive.
Definition _index' : ident := 53%positive.
Definition _start' : ident := 57%positive.
Definition _start'2 : ident := 61%positive.
Definition _start'1 : ident := 59%positive.
Definition _index'2 : ident := 58%positive.
Definition _index'3 : ident := 60%positive.
Definition _index'1 : ident := 55%positive.


Definition f_loop := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_k, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Omod
                 (Ebinop Oadd
                   (Ebinop Omod (Etempvar _k tint)
                     (Econst_int (Int.repr 100) tint) tint)
                   (Econst_int (Int.repr 100) tint) tint)
                 (Econst_int (Int.repr 100) tint) tint)))
|}.

Definition f_find_empty := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_busybits, (tptr tint)) :: (_start, tint) :: (_i, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_index, tint) :: (_bb, tint) :: (54%positive, tint) ::
               (_index', tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _index')
      (Evar _loop (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Ebinop Oadd
         (Ebinop Oadd (Econst_int (Int.repr 1) tint) (Etempvar _start tint)
           tint) (Etempvar _i tint) tint) :: nil))
    (Sset _index (Etempvar _index' tint)))
  (Ssequence
    (Sset _bb
      (Ederef
        (Ebinop Oadd (Etempvar _busybits (tptr tint)) (Etempvar _index tint)
          (tptr tint)) tint))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 0) tint)
                     (Etempvar _bb tint) tint)
        (Sreturn (Some (Etempvar _index tint)))
        Sskip)
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 0) tint)
                       (Etempvar _i tint) tint)
          (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
          Sskip)
        (Ssequence
          (Scall (Some 54%positive)
            (Evar _find_empty (Tfunction
                                (Tcons (tptr tint)
                                  (Tcons tint (Tcons tint Tnil))) tint
                                cc_default))
            ((Etempvar _busybits (tptr tint)) :: (Etempvar _start tint) ::
             (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
               tint) :: nil))
          (Sreturn (Some (Etempvar 54%positive tint))))))))
|}.

Definition f_find_key := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_busybits, (tptr tint)) :: (_keys, (tptr tint)) ::
                (_start, tint) :: (_key, tint) :: (_i, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_index, tint) :: (_bb, tint) :: (_k, tint) ::
               (56%positive, tint) :: (_index'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _index'1)
      (Evar _loop (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Ebinop Oadd
         (Ebinop Oadd (Econst_int (Int.repr 1) tint) (Etempvar _start tint)
           tint) (Etempvar _i tint) tint) :: nil))
    (Sset _index (Etempvar _index'1 tint)))
  (Ssequence
    (Sset _bb
      (Ederef
        (Ebinop Oadd (Etempvar _busybits (tptr tint)) (Etempvar _index tint)
          (tptr tint)) tint))
    (Ssequence
      (Sset _k
        (Ederef
          (Ebinop Oadd (Etempvar _keys (tptr tint)) (Etempvar _index tint)
            (tptr tint)) tint))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 1) tint)
                       (Etempvar _bb tint) tint)
          (Sifthenelse (Ebinop Oeq (Etempvar _k tint) (Etempvar _key tint)
                         tint)
            (Sreturn (Some (Etempvar _index tint)))
            Sskip)
          Sskip)
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _i tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
            Sskip)
          (Ssequence
            (Scall (Some 56%positive)
              (Evar _find_key (Tfunction
                                (Tcons (tptr tint)
                                  (Tcons (tptr tint)
                                    (Tcons tint
                                      (Tcons tint (Tcons tint Tnil))))) tint
                                cc_default))
              ((Etempvar _busybits (tptr tint)) ::
               (Etempvar _keys (tptr tint)) :: (Etempvar _start tint) ::
               (Etempvar _key tint) ::
               (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                 tint) :: nil))
            (Sreturn (Some (Etempvar 56%positive tint)))))))))
|}.

Definition f_get := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_busybits, (tptr tint)) :: (_keys, (tptr tint)) ::
                (_values, (tptr tint)) :: (_key, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_start, tint) :: (_index, tint) :: (_val, tint) ::
               (_index'2, tint) :: (_start', tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _start')
      (Evar _loop (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Etempvar _key tint) :: nil))
    (Sset _start (Etempvar _start' tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _index'2)
        (Evar _find_key (Tfunction
                          (Tcons (tptr tint)
                            (Tcons (tptr tint)
                              (Tcons tint (Tcons tint (Tcons tint Tnil)))))
                          tint cc_default))
        ((Etempvar _busybits (tptr tint)) :: (Etempvar _keys (tptr tint)) ::
         (Etempvar _start tint) :: (Etempvar _key tint) ::
         (Econst_int (Int.repr 99) tint) :: nil))
      (Sset _index (Etempvar _index'2 tint)))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                     (Etempvar _index tint) tint)
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
        Sskip)
      (Ssequence
        (Sset _val
          (Ederef
            (Ebinop Oadd (Etempvar _values (tptr tint))
              (Etempvar _index tint) (tptr tint)) tint))
        (Sreturn (Some (Etempvar _val tint)))))))
|}.

Definition f_put := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_busybits, (tptr tint)) :: (_keys, (tptr tint)) ::
                (_values, (tptr tint)) :: (_key, tint) :: (_value, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_start, tint) :: (_index, tint) :: (_index'3, tint) ::
               (_start'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _start'1)
      (Evar _loop (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Etempvar _key tint) :: nil))
    (Sset _start (Etempvar _start'1 tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _index'3)
        (Evar _find_empty (Tfunction
                            (Tcons (tptr tint)
                              (Tcons tint (Tcons tint Tnil))) tint
                            cc_default))
        ((Etempvar _busybits (tptr tint)) :: (Etempvar _start tint) ::
         (Econst_int (Int.repr 99) tint) :: nil))
      (Sset _index (Etempvar _index'3 tint)))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                     (Etempvar _index tint) tint)
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
        Sskip)
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _busybits (tptr tint))
              (Etempvar _index tint) (tptr tint)) tint)
          (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _keys (tptr tint))
                (Etempvar _index tint) (tptr tint)) tint)
            (Etempvar _key tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _values (tptr tint))
                  (Etempvar _index tint) (tptr tint)) tint)
              (Etempvar _value tint))
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
|}.

Definition f_erase := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_busybits, (tptr tint)) :: (_keys, (tptr tint)) ::
                (_key, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_start, tint) :: (_index, tint) :: (_index'4, tint) ::
               (_start'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _start'2)
      (Evar _loop (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Etempvar _key tint) :: nil))
    (Sset _start (Etempvar _start'2 tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _index'4)
        (Evar _find_key (Tfunction
                          (Tcons (tptr tint)
                            (Tcons (tptr tint)
                              (Tcons tint (Tcons tint (Tcons tint Tnil)))))
                          tint cc_default))
        ((Etempvar _busybits (tptr tint)) :: (Etempvar _keys (tptr tint)) ::
         (Etempvar _start tint) :: (Etempvar _key tint) ::
         (Econst_int (Int.repr 99) tint) :: nil))
      (Sset _index (Etempvar _index'4 tint)))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                     (Etempvar _index tint) tint)
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
        Sskip)
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _busybits (tptr tint))
              (Etempvar _index tint) (tptr tint)) tint)
          (Econst_int (Int.repr 0) tint))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_size_rec := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_busybits, (tptr tint)) :: (_i, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_index, tint) :: (_bb, tint) :: (64%positive, tint) ::
               (63%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 0) tint) (Etempvar _i tint)
                 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Sset _index
      (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))
    (Ssequence
      (Sset _bb
        (Ederef
          (Ebinop Oadd (Etempvar _busybits (tptr tint))
            (Etempvar _index tint) (tptr tint)) tint))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 1) tint)
                       (Etempvar _bb tint) tint)
          (Ssequence
            (Scall (Some 63%positive)
              (Evar _size_rec (Tfunction
                                (Tcons (tptr tint) (Tcons tint Tnil)) tint
                                cc_default))
              ((Etempvar _busybits (tptr tint)) ::
               (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                 tint) :: nil))
            (Sreturn (Some (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                             (Etempvar 63%positive tint) tint))))
          Sskip)
        (Ssequence
          (Scall (Some 64%positive)
            (Evar _size_rec (Tfunction (Tcons (tptr tint) (Tcons tint Tnil))
                              tint cc_default))
            ((Etempvar _busybits (tptr tint)) ::
             (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
               tint) :: nil))
          (Sreturn (Some (Etempvar 64%positive tint))))))))
|}.

Definition f_size := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_busybits, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((65%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some 65%positive)
    (Evar _size_rec (Tfunction (Tcons (tptr tint) (Tcons tint Tnil)) tint
                      cc_default))
    ((Etempvar _busybits (tptr tint)) :: (Econst_int (Int.repr 100) tint) ::
     nil))
  (Sreturn (Some (Etempvar 65%positive tint))))
|}.

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
   Gfun(External (EF_builtin ___builtin_fabs
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin ___builtin_memcpy_aligned
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin ___builtin_annot
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin ___builtin_membar
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin ___builtin_va_start
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin ___builtin_va_arg
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin ___builtin_va_copy
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin ___builtin_va_end
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external ___compcert_va_int32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external ___compcert_va_int64
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external ___compcert_va_float64
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin ___builtin_bswap
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin ___builtin_bswap32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin ___builtin_bswap16
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin ___builtin_clz
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin ___builtin_ctz
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin ___builtin_fsqrt
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin ___builtin_fmax
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin ___builtin_fmin
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin ___builtin_fmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin ___builtin_fmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin ___builtin_fnmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin ___builtin_fnmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin ___builtin_read16_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin ___builtin_read32_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin ___builtin_write16_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin ___builtin_write32_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) :: (_loop, Gfun(Internal f_loop)) ::
 (_find_empty, Gfun(Internal f_find_empty)) ::
 (_find_key, Gfun(Internal f_find_key)) :: (_get, Gfun(Internal f_get)) ::
 (_put, Gfun(Internal f_put)) :: (_erase, Gfun(Internal f_erase)) ::
 (_size_rec, Gfun(Internal f_size_rec)) :: (_size, Gfun(Internal f_size)) ::
 nil);
prog_main := _main
|}.

