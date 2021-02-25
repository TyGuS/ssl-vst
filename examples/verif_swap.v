
Require Import VST.floyd.proofauto.
Require Import swap.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.



Definition swap_spec :=
  DECLARE _swap
   WITH x: val, y: val, a: val, b: val
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x : val)); is_pointer_or_null((y : val)); is_pointer_or_null((a : val)); is_pointer_or_null((b : val)) )
   PARAMS(x; y)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (a : val))] (x : val)); (data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (b : val))] (y : val)))
   POST[ tvoid ]
   PROP(  )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (b : val))] (x : val)); (data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (a : val))] (y : val))).


Definition Gprog : funspecs :=
  ltac:(with_library prog [swap_spec]).

Lemma body_swap : semax_body Vprog Gprog f_swap swap_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr x). { entailer!. }
assert_PROP (isptr y). { entailer!. }
try rename a into a2.
forward.
try rename b into b2.
forward.
forward.
forward.
forward; entailer!.

Qed.