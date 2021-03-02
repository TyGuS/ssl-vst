
Require Import VST.floyd.proofauto.
Require Import common_predicates.
Require Import dll_append.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.













Definition dll_append_spec :=
  DECLARE _dll_append
   WITH x1: val, r: val, x2: val, s2: (list Z), b: val, a: val, _alpha_537: dll_card, s1: (list Z), _alpha_536: dll_card
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x1 : val)); is_pointer_or_null((r : val)); is_pointer_or_null((x2 : val)); is_pointer_or_null((b : val)); is_pointer_or_null((a : val)) )
   PARAMS(x1; r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x2 : val))] (r : val)); (dll (x1 : val) (a : val) (s1 : list Z) (_alpha_536 : dll_card)); (dll (x2 : val) (b : val) (s2 : list Z) (_alpha_537 : dll_card)))
   POST[ tvoid ]
   EX _alpha_538: dll_card,
   EX y: val,
   EX s: (list Z),
   EX c: val,
   PROP( ((s : list Z) = ((s1 : list Z) ++ (s2 : list Z))); is_pointer_or_null((y : val)); is_pointer_or_null((c : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (r : val)); (dll (y : val) (c : val) (s : list Z) (_alpha_538 : dll_card))).






Definition Gprog : funspecs :=
  ltac:(with_library prog [dll_append_spec]).


Lemma body_dll_append : semax_body Vprog Gprog f_dll_append dll_append_spec.
Proof.

start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename x2 into x22.
forward.
forward_if.

 - {
assert_PROP (_alpha_536 = dll_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card dll ssl_card_assert .
assert_PROP (((x1 : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s1 = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.
Exists (_alpha_537 : dll_card).
Exists (x22 : val).
Exists (([] : list Z) ++ (s2 : list Z)).
Exists (b : val).
ssl_entailer.

}
 - {
assert_PROP (exists _alpha_535, _alpha_536 = dll_card_1 _alpha_535) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card dll ssl_card_assert _alpha_535x1.
assert_PROP ((~ ((x1 : val) = nullval))). { entailer!. }
Intros vx1 s1x1 wx1.
let ssl_var := fresh in assert_PROP(s1 = (([(vx1 : Z)] : list Z) ++ (s1x1 : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx1 into vx12.
forward.
try rename wx1 into wx12.
forward.
try rename a into a2.
forward.
assert_PROP(is_pointer_or_null((wx12 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((r : val))). { entailer!. }
assert_PROP(is_pointer_or_null((x22 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((b : val))). { entailer!. }
assert_PROP(is_pointer_or_null((x1 : val))). { entailer!. }
forward_call ((wx12 : val), (r : val), (x22 : val), (s2 : list Z), (b : val), (x1 : val), (_alpha_537 : dll_card), (s1x1 : list Z), (_alpha_535x1 : dll_card)).
let ret := fresh vret in Intros ret; destruct ret as [[[_alpha_5381 y1] s3] c1].
assert_PROP(is_pointer_or_null((y1 : val))). { entailer!. }
let ssl_var := fresh in assert_PROP(s3 = ((s1x1 : list Z) ++ (s2 : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename y1 into y12.
forward.
forward_if.

 - {
assert_PROP (_alpha_5381 = dll_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card dll ssl_card_assert .
assert_PROP (((y12 : val) = nullval)). { entailer!. }
forward.
forward.
forward; entailer!.
Exists (dll_card_1 (dll_card_0  : dll_card) : dll_card).
Exists (x1 : val).
Exists ((([(vx12 : Z)] : list Z) ++ (s1x1 : list Z)) ++ (s2 : list Z)).
Exists (a2 : val).
ssl_entailer.
rewrite (unfold_dll_card_1 (dll_card_0  : dll_card)) at 1.
Exists (vx12 : Z).
Exists ([] : list Z).
Exists nullval.
ssl_entailer.
rewrite (unfold_dll_card_0 ) at 1.
ssl_entailer.

}
 - {
assert_PROP (exists _alpha_535, _alpha_5381 = dll_card_1 _alpha_535) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card dll ssl_card_assert _alpha_535y12.
assert_PROP ((~ ((y12 : val) = nullval))). { entailer!. }
Intros vy12 s1y12 wy12.
try rename vy12 into vy122.
forward.
try rename wy12 into wy122.
forward.
try rename c1 into c12.
forward.
forward.
forward.
forward.
forward; entailer!.
Exists (dll_card_1 (dll_card_1 (_alpha_535y12 : dll_card) : dll_card) : dll_card).
Exists (x1 : val).
Exists ((([(vx12 : Z)] : list Z) ++ (s1x1 : list Z)) ++ (s2 : list Z)).
Exists (a2 : val).
ssl_entailer.
rewrite (unfold_dll_card_1 (dll_card_1 (_alpha_535y12 : dll_card) : dll_card)) at 1.
Exists (vx12 : Z).
Exists (([(vy122 : Z)] : list Z) ++ (s1y12 : list Z)).
Exists (y12 : val).
ssl_entailer.
rewrite (unfold_dll_card_1 (_alpha_535y12 : dll_card)) at 1.
Exists (vy122 : Z).
Exists (s1y12 : list Z).
Exists (wy122 : val).
ssl_entailer.

}
}

Qed.