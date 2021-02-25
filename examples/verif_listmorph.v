
Require Import VST.floyd.proofauto.
Require Import listmorph.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Inductive lseg_card : Set :=
    | lseg_card_0 : lseg_card
    | lseg_card_1 : lseg_card -> lseg_card.

Fixpoint lseg (x: val) (s: (list Z)) (self_card: lseg_card) {struct self_card} : mpred := match self_card with
    | lseg_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | lseg_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (lseg (nxt : val) (s1 : list Z) (_alpha_513 : lseg_card))
end.

Inductive lseg2_card : Set :=
    | lseg2_card_0 : lseg2_card
    | lseg2_card_1 : lseg2_card -> lseg2_card.

Fixpoint lseg2 (x: val) (y: val) (s: (list Z)) (self_card: lseg2_card) {struct self_card} : mpred := match self_card with
    | lseg2_card_0  =>  !!((x : val) = (y : val)) && !!((s : list Z) = ([] : list Z)) && emp
    | lseg2_card_1 _alpha_514 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = (y : val))) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (lseg2 (nxt : val) (y : val) (s1 : list Z) (_alpha_514 : lseg2_card))
end.


Definition listmorph_spec :=
  DECLARE _listmorph
   WITH x: val, r: val, s: (list Z), _alpha_515: lseg2_card
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x : val)); is_pointer_or_null((r : val)) )
   PARAMS(x; r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr nullval)] (r : val)); (lseg2 (x : val) nullval (s : list Z) (_alpha_515 : lseg2_card)))
   POST[ tvoid ]
   EX y: val,
   EX _alpha_516: lseg_card,
   PROP(  )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (r : val)); (lseg (y : val) (s : list Z) (_alpha_516 : lseg_card))).

Lemma lseg_x_valid_pointerP x s self_card: lseg x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve lseg_x_valid_pointerP : valid_pointer.
Lemma lseg_local_factsP x s self_card :
  lseg x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = lseg_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_513, self_card = lseg_card_1 _alpha_513))/\is_pointer_or_null((x : val))). Proof. Admitted.
Hint Resolve lseg_local_factsP : saturate_local.
Lemma unfold_lseg_card_0  (x: val) (s: (list Z)) : lseg x s (lseg_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_lseg_card_1 (_alpha_513 : lseg_card) (x: val) (s: (list Z)) : lseg x s (lseg_card_1 _alpha_513) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (lseg (nxt : val) (s1 : list Z) (_alpha_513 : lseg_card)). Proof. auto. Qed.
Lemma lseg2_x_valid_pointerP x y s self_card: lseg2 x y s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve lseg2_x_valid_pointerP : valid_pointer.
Lemma lseg2_y_valid_pointerP x y s self_card: lseg2 x y s self_card |-- valid_pointer y. Proof. Admitted.
Hint Resolve lseg2_y_valid_pointerP : valid_pointer.
Lemma lseg2_local_factsP x y s self_card :
  lseg2 x y s self_card|-- !!(((((x : val) = (y : val))) -> (self_card = lseg2_card_0))/\(((~ ((x : val) = (y : val)))) -> (exists _alpha_514, self_card = lseg2_card_1 _alpha_514))/\is_pointer_or_null((x : val))/\is_pointer_or_null((y : val))). Proof. Admitted.
Hint Resolve lseg2_local_factsP : saturate_local.
Lemma unfold_lseg2_card_0  (x: val) (y: val) (s: (list Z)) : lseg2 x y s (lseg2_card_0 ) =  !!((x : val) = (y : val)) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_lseg2_card_1 (_alpha_514 : lseg2_card) (x: val) (y: val) (s: (list Z)) : lseg2 x y s (lseg2_card_1 _alpha_514) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = (y : val))) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (lseg2 (nxt : val) (y : val) (s1 : list Z) (_alpha_514 : lseg2_card)). Proof. auto. Qed.
Definition Gprog : funspecs :=
  ltac:(with_library prog [listmorph_spec]).

Lemma body_listmorph : semax_body Vprog Gprog f_listmorph listmorph_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
forward_if.

 - {
assert_PROP (_alpha_515 = lseg2_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card lseg2 ssl_card_assert .
assert_PROP (((x : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.
Exists nullval.
Exists (lseg_card_0  : lseg_card).
ssl_entailer.
ssl_rewrite_last (unfold_lseg_card_0 ).
ssl_entailer.

}
 - {
assert_PROP (exists _alpha_514, _alpha_515 = lseg2_card_1 _alpha_514) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card lseg2 ssl_card_assert _alpha_514x.
assert_PROP ((~ ((x : val) = nullval))). { entailer!. }
Intros vx s1x nxtx.
let ssl_var := fresh in assert_PROP(s = (([(vx : Z)] : list Z) ++ (s1x : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx into vx2.
forward.
try rename nxtx into nxtx2.
forward.
assert_PROP(is_pointer_or_null((nxtx2 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((r : val))). { entailer!. }
forward_call ((nxtx2 : val), (r : val), (s1x : list Z), (_alpha_514x : lseg2_card)).
let ret := fresh vret in Intros ret; destruct ret as [y1 _alpha_5161].
assert_PROP(is_pointer_or_null((y1 : val))). { entailer!. }
try rename y1 into y12.
forward.
forward.
forward.
forward; entailer!.
Exists (x : val).
Exists (lseg_card_1 (_alpha_5161 : lseg_card) : lseg_card).
ssl_entailer.
ssl_rewrite_last (unfold_lseg_card_1 (_alpha_5161 : lseg_card)).
Exists (vx2 : Z).
Exists (s1x : list Z).
Exists (y12 : val).
ssl_entailer.

}
Qed.