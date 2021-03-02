
Require Import VST.floyd.proofauto.
Require Import common_predicates.
Require Import min2.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.













Definition min2_spec :=
  DECLARE _min2
   WITH r: val, x: val, y: val
   PRE [ (tptr (Tunion _sslval noattr)), tint, tint ]
   PROP( is_pointer_or_null((r : val)); ssl_is_valid_int((x : val)); ssl_is_valid_int((y : val)) )
   PARAMS(r; x; y)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr nullval)] (r : val)))
   POST[ tvoid ]
   EX m: Z,
   PROP( ((m : Z) <= (force_signed_int (x : val))); ((m : Z) <= (force_signed_int (y : val))) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inl ((Vint (Int.repr m)) : val))] (r : val))).






Definition Gprog : funspecs :=
  ltac:(with_library prog [min2_spec]).


Lemma body_min2 : semax_body Vprog Gprog f_min2 min2_spec.
Proof.

start_function.
ssl_open_context.
forward_if.

 - {
assert_PROP (isptr r). { entailer!. }
forward.
forward; entailer!.
Exists (x : Z).
ssl_entailer.

}
 - {
assert_PROP (isptr r). { entailer!. }
forward.
forward; entailer!.
Exists (y : Z).
ssl_entailer.

}

Qed.