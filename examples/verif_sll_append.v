
Require Import VST.floyd.proofauto.
Require Import sll_append.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: val) (s: (list Z)) (self_card: sll_card) {struct self_card} : mpred := match self_card with
    | sll_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | sll_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_513 : sll_card))
end.


Definition sll_append_spec :=
  DECLARE _sll_append
   WITH x1: val, r: val, _alpha_515: sll_card, x2: val, s2: (list Z), s1: (list Z), _alpha_514: sll_card
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x1 : val)); is_pointer_or_null((r : val)); is_pointer_or_null((x2 : val)) )
   PARAMS(x1; r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x2 : val))] (r : val)); (sll (x1 : val) (s1 : list Z) (_alpha_514 : sll_card)); (sll (x2 : val) (s2 : list Z) (_alpha_515 : sll_card)))
   POST[ tvoid ]
   EX y: val,
   EX s: (list Z),
   EX _alpha_516: sll_card,
   PROP( ((s : list Z) = ((s1 : list Z) ++ (s2 : list Z))); is_pointer_or_null((y : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (r : val)); (sll (y : val) (s : list Z) (_alpha_516 : sll_card))).

Lemma sll_x_valid_pointerP x s self_card: sll x s self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x s self_card :
  sll x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = sll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_513, self_card = sll_card_1 _alpha_513))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve sll_local_factsP : saturate_local.
Lemma unfold_sll_card_0  (x: val) (s: (list Z)) : sll x s (sll_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_sll_card_1 (_alpha_513 : sll_card) (x: val) (s: (list Z)) : sll x s (sll_card_1 _alpha_513) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_513 : sll_card)). Proof. auto. Qed.
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
assert_PROP (_alpha_514 = sll_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert .
assert_PROP (((x1 : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s1 = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.
Exists (x22 : val).
Exists (([] : list Z) ++ (s2 : list Z)).
Exists (_alpha_515 : sll_card).
ssl_entailer.

}
 - {
assert_PROP (exists _alpha_513, _alpha_514 = sll_card_1 _alpha_513) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card sll ssl_card_assert _alpha_513x1.
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
forward_call ((nxtx12 : val), (r : val), (_alpha_515 : sll_card), (x22 : val), (s2 : list Z), (s1x1 : list Z), (_alpha_513x1 : sll_card)).
let ret := fresh vret in Intros ret; destruct ret as [[y1 s3] _alpha_5161].
assert_PROP(is_pointer_or_null((y1 : val))). { entailer!. }
let ssl_var := fresh in assert_PROP(s3 = ((s1x1 : list Z) ++ (s2 : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename y1 into y12.
forward.
forward.
forward.
forward; entailer!.
Exists (x1 : val).
Exists ((([(vx12 : Z)] : list Z) ++ (s1x1 : list Z)) ++ (s2 : list Z)).
Exists (sll_card_1 (_alpha_5161 : sll_card) : sll_card).
ssl_entailer.
rewrite (unfold_sll_card_1 (_alpha_5161 : sll_card)) at 1.
Exists (vx12 : Z).
Exists ((s1x1 : list Z) ++ (s2 : list Z)).
Exists (y12 : val).
ssl_entailer.

}
Qed.