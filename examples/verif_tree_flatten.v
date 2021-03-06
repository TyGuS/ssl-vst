
Require Import VST.floyd.proofauto.
Require Import tree_flatten.
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

Definition malloc_spec :=
  DECLARE _malloc
        WITH t: type
        PRE [ tuint ]
        PROP()
        PARAMS(Vint (Int.repr (sizeof t)))
        SEP()
        POST [tptr tvoid] EX p:_,
        PROP()
        RETURN(p)
        SEP(data_at_ Tsh t p).

Inductive tree_card : Set :=
    | tree_card_0 : tree_card
    | tree_card_2 : tree_card -> tree_card -> tree_card.

Fixpoint tree (x: val) (s: (list Z)) (self_card: tree_card) {struct self_card} : mpred := match self_card with
    | tree_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | tree_card_2 _alpha_514 _alpha_513 => 
      EX v : Z,
      EX s2 : (list Z),
      EX r : val,
      EX s1 : (list Z),
      EX l : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null r) && !!(is_pointer_or_null l) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = ((([(v : Z)] : list Z) ++ (s1 : list Z)) ++ (s2 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (tree (l : val) (s1 : list Z) (_alpha_513 : tree_card)) * (tree (r : val) (s2 : list Z) (_alpha_514 : tree_card))
end.

Inductive treeN_card : Set :=
    | treeN_card_0 : treeN_card
    | treeN_card_2 : treeN_card -> treeN_card -> treeN_card.

Fixpoint treeN (x: val) (n: Z) (self_card: treeN_card) {struct self_card} : mpred := match self_card with
    | treeN_card_0  =>  !!((x : val) = nullval) && !!((n : Z) = 0) && emp
    | treeN_card_2 _alpha_516 _alpha_515 => 
      EX n1 : Z,
      EX v : val,
      EX r : val,
      EX n2 : Z,
      EX l : val,
 !!(Int.min_signed <= n1 <= Int.max_signed) && !!(is_pointer_or_null v) && !!(is_pointer_or_null r) && !!(Int.min_signed <= n2 <= Int.max_signed) && !!(is_pointer_or_null l) && !!(~ ((x : val) = nullval)) && !!(0 <= (n1 : Z)) && !!(0 <= (n2 : Z)) && !!((n : Z) = ((1 + (n1 : Z)) + (n2 : Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inr (v : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (treeN (l : val) (n1 : Z) (_alpha_515 : treeN_card)) * (treeN (r : val) (n2 : Z) (_alpha_516 : treeN_card))
end.

Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: val) (s: (list Z)) (self_card: sll_card) {struct self_card} : mpred := match self_card with
    | sll_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | sll_card_1 _alpha_517 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_517 : sll_card))
end.

Definition sll_append_spec :=
  DECLARE _sll_append
   WITH x1: val, ret: val, _alpha_519: sll_card, _alpha_518: sll_card, x2: val, s2: (list Z), s1: (list Z)
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x1 : val)); is_pointer_or_null((ret : val)); is_pointer_or_null((x2 : val)) )
   PARAMS(x1; ret)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x2 : val))] (ret : val)); (sll (x1 : val) (s1 : list Z) (_alpha_518 : sll_card)); (sll (x2 : val) (s2 : list Z) (_alpha_519 : sll_card)))
   POST[ tvoid ]
   EX y: val,
   EX _alpha_520: sll_card,
   EX s: (list Z),
   PROP( ((s : list Z) = ((s1 : list Z) ++ (s2 : list Z))); is_pointer_or_null((y : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (ret : val)); (sll (y : val) (s : list Z) (_alpha_520 : sll_card))).

Definition tree_flatten_spec :=
  DECLARE _tree_flatten
   WITH z: val, x: val, s: (list Z), _alpha_521: tree_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((z : val)); is_pointer_or_null((x : val)) )
   PARAMS(z)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x : val))] (z : val)); (tree (x : val) (s : list Z) (_alpha_521 : tree_card)))
   POST[ tvoid ]
   EX y: val,
   EX _alpha_522: sll_card,
   PROP( is_pointer_or_null((y : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (z : val)); (sll (y : val) (s : list Z) (_alpha_522 : sll_card))).

Lemma tree_x_valid_pointerP x s self_card: tree x s self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve tree_x_valid_pointerP : valid_pointer.
Lemma tree_local_factsP x s self_card :
  tree x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = tree_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_514 _alpha_513, self_card = tree_card_2 _alpha_514 _alpha_513))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve tree_local_factsP : saturate_local.
Lemma unfold_tree_card_0  (x: val) (s: (list Z)) : tree x s (tree_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_tree_card_2 (_alpha_514 : tree_card) (_alpha_513 : tree_card) (x: val) (s: (list Z)) : tree x s (tree_card_2 _alpha_514 _alpha_513) = 
      EX v : Z,
      EX s2 : (list Z),
      EX r : val,
      EX s1 : (list Z),
      EX l : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null r) && !!(is_pointer_or_null l) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = ((([(v : Z)] : list Z) ++ (s1 : list Z)) ++ (s2 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (tree (l : val) (s1 : list Z) (_alpha_513 : tree_card)) * (tree (r : val) (s2 : list Z) (_alpha_514 : tree_card)). Proof. auto. Qed.
Lemma treeN_x_valid_pointerP x n self_card: treeN x n self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve treeN_x_valid_pointerP : valid_pointer.
Lemma treeN_local_factsP x n self_card :
  treeN x n self_card|-- !!(((((x : val) = nullval)) -> (self_card = treeN_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_516 _alpha_515, self_card = treeN_card_2 _alpha_516 _alpha_515))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve treeN_local_factsP : saturate_local.
Lemma unfold_treeN_card_0  (x: val) (n: Z) : treeN x n (treeN_card_0 ) =  !!((x : val) = nullval) && !!((n : Z) = 0) && emp. Proof. auto. Qed.
Lemma unfold_treeN_card_2 (_alpha_516 : treeN_card) (_alpha_515 : treeN_card) (x: val) (n: Z) : treeN x n (treeN_card_2 _alpha_516 _alpha_515) = 
      EX n1 : Z,
      EX v : val,
      EX r : val,
      EX n2 : Z,
      EX l : val,
 !!(Int.min_signed <= n1 <= Int.max_signed) && !!(is_pointer_or_null v) && !!(is_pointer_or_null r) && !!(Int.min_signed <= n2 <= Int.max_signed) && !!(is_pointer_or_null l) && !!(~ ((x : val) = nullval)) && !!(0 <= (n1 : Z)) && !!(0 <= (n2 : Z)) && !!((n : Z) = ((1 + (n1 : Z)) + (n2 : Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inr (v : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (treeN (l : val) (n1 : Z) (_alpha_515 : treeN_card)) * (treeN (r : val) (n2 : Z) (_alpha_516 : treeN_card)). Proof. auto. Qed.
Lemma sll_x_valid_pointerP x s self_card: sll x s self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x s self_card :
  sll x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = sll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_517, self_card = sll_card_1 _alpha_517))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve sll_local_factsP : saturate_local.
Lemma unfold_sll_card_0  (x: val) (s: (list Z)) : sll x s (sll_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_sll_card_1 (_alpha_517 : sll_card) (x: val) (s: (list Z)) : sll x s (sll_card_1 _alpha_517) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_517 : sll_card)). Proof. auto. Qed.
Definition Gprog : funspecs :=
  ltac:(with_library prog [tree_flatten_spec; free_spec; malloc_spec;sll_append_spec]).

Lemma body_tree_flatten : semax_body Vprog Gprog f_tree_flatten tree_flatten_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr z). { entailer!. }
try rename x into x2.
forward.
forward_if.

 - {
assert_PROP (_alpha_521 = tree_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert .
assert_PROP (((x2 : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.
Exists nullval.
Exists (sll_card_0  : sll_card).
ssl_entailer.
rewrite (unfold_sll_card_0 ) at 1.
ssl_entailer.

}
 - {
assert_PROP (exists _alpha_514 _alpha_513, _alpha_521 = tree_card_2 _alpha_514 _alpha_513) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert _alpha_514x2 _alpha_513x2.
assert_PROP ((~ ((x2 : val) = nullval))). { entailer!. }
Intros vx2 s2x2 rx2 s1x2 lx2.
let ssl_var := fresh in assert_PROP(s = ((([(vx2 : Z)] : list Z) ++ (s1x2 : list Z)) ++ (s2x2 : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx2 into vx22.
forward.
try rename lx2 into lx22.
forward.
try rename rx2 into rx22.
forward.
forward.
assert_PROP(is_pointer_or_null((z : val))). { entailer!. }
assert_PROP(is_pointer_or_null((lx22 : val))). { entailer!. }
forward_call ((z : val), (lx22 : val), (s1x2 : list Z), (_alpha_513x2 : tree_card)).
let ret := fresh vret in Intros ret; destruct ret as [y1 _alpha_5221].
assert_PROP(is_pointer_or_null((y1 : val))). { entailer!. }
try rename y1 into y12.
forward.
forward.
assert_PROP(is_pointer_or_null((z : val))). { entailer!. }
assert_PROP(is_pointer_or_null((rx22 : val))). { entailer!. }
forward_call ((z : val), (rx22 : val), (s2x2 : list Z), (_alpha_514x2 : tree_card)).
let ret := fresh vret in Intros ret; destruct ret as [y2 _alpha_5222].
assert_PROP(is_pointer_or_null((y2 : val))). { entailer!. }
try rename y2 into y22.
forward.
assert_PROP(is_pointer_or_null((y12 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((z : val))). { entailer!. }
assert_PROP(is_pointer_or_null((y22 : val))). { entailer!. }
forward_call ((y12 : val), (z : val), (_alpha_5222 : sll_card), (_alpha_5221 : sll_card), (y22 : val), (s2x2 : list Z), (s1x2 : list Z)).
ssl_entailer.
let ret := fresh vret in Intros ret; destruct ret as [[y3 _alpha_520] s3].
assert_PROP(is_pointer_or_null((y3 : val))). { entailer!. }
let ssl_var := fresh in assert_PROP(s3 = ((s1x2 : list Z) ++ (s2x2 : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename y3 into y32.
forward.
forward_call (tarray (Tunion _sslval noattr) 2).
Intros y4.
assert_PROP (isptr y4). { entailer!. }
forward_call (tarray (Tunion _sslval noattr) 3, x2).
forward.
forward.
forward.
forward; entailer!.
Exists (y4 : val).
Exists (sll_card_1 (_alpha_520 : sll_card) : sll_card).
ssl_entailer.
rewrite (unfold_sll_card_1 (_alpha_520 : sll_card)) at 1.
Exists (vx22 : Z).
Exists ((s1x2 : list Z) ++ (s2x2 : list Z)).
Exists (y32 : val).
ssl_entailer.

}
Qed.