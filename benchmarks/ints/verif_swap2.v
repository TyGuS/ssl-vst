
Require Import VST.floyd.proofauto.
Require Import common_predicates.
Require Import swap2.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.













Definition swap2_spec :=
  DECLARE _swap2
   WITH x: val, z: val, y: val, t: val, q: val, c: val, b: val, a: val
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x : val)); is_pointer_or_null((z : val)); is_pointer_or_null((y : val)); is_pointer_or_null((t : val)); is_pointer_or_null((q : val)); is_pointer_or_null((c : val)); is_pointer_or_null((b : val)); is_pointer_or_null((a : val)) )
   PARAMS(x; z; y; t)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (a : val))] (x : val)); (data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (c : val))] (y : val)); (data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (b : val))] (z : val)); (data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (q : val))] (t : val)))
   POST[ tvoid ]
   PROP(  )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (q : val))] (x : val)); (data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (c : val))] (z : val)); (data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (a : val))] (t : val)); (data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (b : val))] (y : val))).






Definition Gprog : funspecs :=
  ltac:(with_library prog [swap2_spec]).


Lemma body_swap2 : semax_body Vprog Gprog f_swap2 swap2_spec.
Proof.

start_function.
ssl_open_context.
assert_PROP (isptr x). { entailer!. }
assert_PROP (isptr y). { entailer!. }
assert_PROP (isptr z). { entailer!. }
assert_PROP (isptr t). { entailer!. }
try rename a into a2.
forward.
try rename c into c2.
forward.
try rename b into b2.
forward.
try rename q into q2.
forward.
forward.
forward.
forward.
forward.
forward; entailer!.


Qed.