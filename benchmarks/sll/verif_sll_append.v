
Require Import VST.floyd.proofauto.
Require Import common_predicates.
Require Import sll_append.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.













Definition sll_append_spec :=
  DECLARE _sll_append
   WITH x1: val, r: val, x2: val, s2: (list Z), _alpha_526: sll_card, _alpha_525: sll_card, s1: (list Z)
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x1 : val)); is_pointer_or_null((r : val)); is_pointer_or_null((x2 : val)) )
   PARAMS(x1; r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x2 : val))] (r : val)); (sll (x1 : val) (s1 : list Z) (_alpha_525 : sll_card)); (sll (x2 : val) (s2 : list Z) (_alpha_526 : sll_card)))
   POST[ tvoid ]
   EX _alpha_527: sll_card,
   EX y: val,
   EX s: (list Z),
   PROP( ((s : list Z) = ((s1 : list Z) ++ (s2 : list Z))); is_pointer_or_null((y : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (r : val)); (sll (y : val) (s : list Z) (_alpha_527 : sll_card))).






Definition Gprog : funspecs :=
  ltac:(with_library prog [sll_append_spec]).


Lemma body_sll_append : semax_body Vprog Gprog f_sll_append sll_append_spec.
Proof.

start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename x2 into x22.
forward.
forward_if.

 - {
assert_PROP (_alpha_525 = sll_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert .
assert_PROP (((x1 : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s1 = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.
Exists (_alpha_526 : sll_card).
Exists (x22 : val).
Exists (([] : list Z) ++ (s2 : list Z)).
ssl_entailer.

}
 - {
assert_PROP (exists _alpha_524, _alpha_525 = sll_card_1 _alpha_524) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert _alpha_524x1.
assert_PROP ((~ ((x1 : val) = nullval))). { entailer!. }
Intros vx1 s1x1 nxtx1.
let ssl_var := fresh in assert_PROP(s1 = (([(vx1 : Z)] : list Z) ++ (s1x1 : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx1 into vx12.
forward.
try rename nxtx1 into nxtx12.
forward.
assert_PROP(is_pointer_or_null((nxtx12 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((r : val))). { entailer!. }
assert_PROP(is_pointer_or_null((x22 : val))). { entailer!. }
forward_call ((nxtx12 : val), (r : val), (x22 : val), (s2 : list Z), (_alpha_526 : sll_card), (_alpha_524x1 : sll_card), (s1x1 : list Z)).
let ret := fresh vret in Intros ret; destruct ret as [[_alpha_5271 y1] s3].
assert_PROP(is_pointer_or_null((y1 : val))). { entailer!. }
let ssl_var := fresh in assert_PROP(s3 = ((s1x1 : list Z) ++ (s2 : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename y1 into y12.
forward.
forward.
forward.
forward; entailer!.
Exists (sll_card_1 (_alpha_5271 : sll_card) : sll_card).
Exists (x1 : val).
Exists ((([(vx12 : Z)] : list Z) ++ (s1x1 : list Z)) ++ (s2 : list Z)).
ssl_entailer.
rewrite (unfold_sll_card_1 (_alpha_5271 : sll_card)) at 1.
Exists (vx12 : Z).
Exists ((s1x1 : list Z) ++ (s2 : list Z)).
Exists (y12 : val).
ssl_entailer.

}

Qed.