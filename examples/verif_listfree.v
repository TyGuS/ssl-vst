
Require Import VST.floyd.proofauto.
Require Import listfree.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition free_spec :=
  DECLARE _free
          WITH ty: type, x: val
                              PRE  [ (tptr tvoid) ]
                              PROP()
                              PARAMS(x)
                              SEP (data_at_ Tsh ty x)
                              POST [ Tvoid ]
                              PROP()
                              LOCAL()
                              SEP (emp).

Inductive lseg_card : Set :=
    | lseg_card_0 : lseg_card
    | lseg_card_1 : lseg_card -> lseg_card.

Fixpoint lseg (x: val) (s: (list Z)) (self_card: lseg_card) {struct self_card} : mpred := match self_card with
    | lseg_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | lseg_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (lseg (nxt : val) (s1 : list Z) (_alpha_513 : lseg_card))
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
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(~ ((x : val) = (y : val))) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (lseg2 (nxt : val) (y : val) (s1 : list Z) (_alpha_514 : lseg2_card))
end.


Definition listfree_spec :=
  DECLARE _listfree
   WITH x: val, s: (list Z), _alpha_515: lseg_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x : val)) )
   PARAMS(x)
   SEP ((lseg (x : val) (s : list Z) (_alpha_515 : lseg_card)))
   POST[ tvoid ]
   PROP(  )
   LOCAL()
   SEP ().

Lemma lseg_x_valid_pointerP x s self_card: lseg x s self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve lseg_x_valid_pointerP : valid_pointer.
Lemma lseg_local_factsP x s self_card :
  lseg x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = lseg_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_513, self_card = lseg_card_1 _alpha_513))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve lseg_local_factsP : saturate_local.
Lemma unfold_lseg_card_0  (x: val) (s: (list Z)) : lseg x s (lseg_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_lseg_card_1 (_alpha_513 : lseg_card) (x: val) (s: (list Z)) : lseg x s (lseg_card_1 _alpha_513) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (lseg (nxt : val) (s1 : list Z) (_alpha_513 : lseg_card)). Proof. auto. Qed.
Lemma lseg2_local_factsP x y s self_card :
  lseg2 x y s self_card|-- !!(((((x : val) = (y : val))) -> (self_card = lseg2_card_0))/\(((~ ((x : val) = (y : val)))) -> (exists _alpha_514, self_card = lseg2_card_1 _alpha_514))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve lseg2_local_factsP : saturate_local.
Lemma unfold_lseg2_card_0  (x: val) (y: val) (s: (list Z)) : lseg2 x y s (lseg2_card_0 ) =  !!((x : val) = (y : val)) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_lseg2_card_1 (_alpha_514 : lseg2_card) (x: val) (y: val) (s: (list Z)) : lseg2 x y s (lseg2_card_1 _alpha_514) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(~ ((x : val) = (y : val))) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (lseg2 (nxt : val) (y : val) (s1 : list Z) (_alpha_514 : lseg2_card)). Proof. auto. Qed.
Definition Gprog : funspecs :=
  ltac:(with_library prog [listfree_spec; free_spec]).

Lemma body_listfree : semax_body Vprog Gprog f_listfree listfree_spec.
Proof.
start_function.
ssl_open_context.
forward_if.

 - {
assert_PROP (_alpha_515 = lseg_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card lseg ssl_card_assert .
assert_PROP (((x : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.

}
 - {
assert_PROP (exists _alpha_513, _alpha_515 = lseg_card_1 _alpha_513) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card lseg ssl_card_assert _alpha_513x.
assert_PROP ((~ ((x : val) = nullval))). { entailer!. }
Intros vx s1x nxtx.
let ssl_var := fresh in assert_PROP(s = (([(vx : Z)] : list Z) ++ (s1x : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx into vx2.
forward.
try rename nxtx into nxtx2.
forward.
assert_PROP(is_pointer_or_null((nxtx2 : val))). { entailer!. }
forward_call ((nxtx2 : val), (s1x : list Z), (_alpha_513x : lseg_card)).
forward_call (tarray (Tunion _sslval noattr) 2, x).
forward; entailer!.

}
Qed.