
Require Import VST.floyd.proofauto.
Require Import tree_flatten_acc.
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
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = ((([(v : Z)] : list Z) ++ (s1 : list Z)) ++ (s2 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (tree (r : val) (s2 : list Z) (_alpha_514 : tree_card)) * (tree (l : val) (s1 : list Z) (_alpha_513 : tree_card))
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
 !!(Int.min_signed <= n1 <= Int.max_signed) && !!(Int.min_signed <= n2 <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!(0 <= (n1 : Z)) && !!(0 <= (n2 : Z)) && !!((n : Z) = ((1 + (n1 : Z)) + (n2 : Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inr (v : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (treeN (r : val) (n2 : Z) (_alpha_516 : treeN_card)) * (treeN (l : val) (n1 : Z) (_alpha_515 : treeN_card))
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
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_517 : sll_card))
end.


Definition tree_flatten_acc_spec :=
  DECLARE _tree_flatten_acc
   WITH x: val, z: val, _alpha_519: sll_card, y: val, _alpha_518: tree_card, acc: (list Z), s: (list Z)
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x : val)); is_pointer_or_null((z : val)); is_pointer_or_null((y : val)) )
   PARAMS(x; z)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (z : val)); (sll (y : val) (acc : list Z) (_alpha_519 : sll_card)); (tree (x : val) (s : list Z) (_alpha_518 : tree_card)))
   POST[ tvoid ]
   EX t: val,
   EX s1: (list Z),
   EX _alpha_520: sll_card,
   PROP( ((s1 : list Z) = ((s : list Z) ++ (acc : list Z))) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (t : val))] (z : val)); (sll (t : val) (s1 : list Z) (_alpha_520 : sll_card))).

Lemma tree_x_valid_pointerP x s self_card: tree x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve tree_x_valid_pointerP : valid_pointer.
Lemma tree_local_factsP x s self_card :
  tree x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = tree_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_514 _alpha_513, self_card = tree_card_2 _alpha_514 _alpha_513))/\is_pointer_or_null((x : val))). Proof. Admitted.
Hint Resolve tree_local_factsP : saturate_local.
Lemma unfold_tree_card_0  (x: val) (s: (list Z)) : tree x s (tree_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_tree_card_2 (_alpha_514 : tree_card) (_alpha_513 : tree_card) (x: val) (s: (list Z)) : tree x s (tree_card_2 _alpha_514 _alpha_513) = 
      EX v : Z,
      EX s2 : (list Z),
      EX r : val,
      EX s1 : (list Z),
      EX l : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = ((([(v : Z)] : list Z) ++ (s1 : list Z)) ++ (s2 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (tree (r : val) (s2 : list Z) (_alpha_514 : tree_card)) * (tree (l : val) (s1 : list Z) (_alpha_513 : tree_card)). Proof. auto. Qed.
Lemma treeN_x_valid_pointerP x n self_card: treeN x n self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve treeN_x_valid_pointerP : valid_pointer.
Lemma treeN_local_factsP x n self_card :
  treeN x n self_card|-- !!(((((x : val) = nullval)) -> (self_card = treeN_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_516 _alpha_515, self_card = treeN_card_2 _alpha_516 _alpha_515))/\is_pointer_or_null((x : val))). Proof. Admitted.
Hint Resolve treeN_local_factsP : saturate_local.
Lemma unfold_treeN_card_0  (x: val) (n: Z) : treeN x n (treeN_card_0 ) =  !!((x : val) = nullval) && !!((n : Z) = 0) && emp. Proof. auto. Qed.
Lemma unfold_treeN_card_2 (_alpha_516 : treeN_card) (_alpha_515 : treeN_card) (x: val) (n: Z) : treeN x n (treeN_card_2 _alpha_516 _alpha_515) = 
      EX n1 : Z,
      EX v : val,
      EX r : val,
      EX n2 : Z,
      EX l : val,
 !!(Int.min_signed <= n1 <= Int.max_signed) && !!(Int.min_signed <= n2 <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!(0 <= (n1 : Z)) && !!(0 <= (n2 : Z)) && !!((n : Z) = ((1 + (n1 : Z)) + (n2 : Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inr (v : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (treeN (r : val) (n2 : Z) (_alpha_516 : treeN_card)) * (treeN (l : val) (n1 : Z) (_alpha_515 : treeN_card)). Proof. auto. Qed.
Lemma sll_x_valid_pointerP x s self_card: sll x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x s self_card :
  sll x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = sll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_517, self_card = sll_card_1 _alpha_517))/\is_pointer_or_null((x : val))). Proof. Admitted.
Hint Resolve sll_local_factsP : saturate_local.
Lemma unfold_sll_card_0  (x: val) (s: (list Z)) : sll x s (sll_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_sll_card_1 (_alpha_517 : sll_card) (x: val) (s: (list Z)) : sll x s (sll_card_1 _alpha_517) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_517 : sll_card)). Proof. auto. Qed.
Definition Gprog : funspecs :=
  ltac:(with_library prog [tree_flatten_acc_spec; free_spec; malloc_spec]).

Lemma body_tree_flatten_acc : semax_body Vprog Gprog f_tree_flatten_acc tree_flatten_acc_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr z). { entailer!. }
try rename y into y2.
forward.
forward_if.

 - {
assert_PROP (_alpha_518 = tree_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert .
assert_PROP (((x : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.
Exists (y2 : val).
Exists (([] : list Z) ++ (acc : list Z)).
Exists (_alpha_519 : sll_card).
ssl_entailer.

}
 - {
assert_PROP (exists _alpha_514 _alpha_513, _alpha_518 = tree_card_2 _alpha_514 _alpha_513) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert _alpha_514x _alpha_513x.
assert_PROP ((~ ((x : val) = nullval))). { entailer!. }
Intros vx s2x rx s1x lx.
let ssl_var := fresh in assert_PROP(s = ((([(vx : Z)] : list Z) ++ (s1x : list Z)) ++ (s2x : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename vx into vx2.
forward.
try rename lx into lx2.
forward.
try rename rx into rx2.
forward.
assert_PROP(is_pointer_or_null((lx2 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((z : val))). { entailer!. }
assert_PROP(is_pointer_or_null((y2 : val))). { entailer!. }
forward_call ((lx2 : val), (z : val), (_alpha_519 : sll_card), (y2 : val), (_alpha_513x : tree_card), (acc : list Z), (s1x : list Z)).
let ret := fresh vret in Intros ret; destruct ret as [[t1 s11] _alpha_5201].
assert_PROP(is_pointer_or_null((t1 : val))). { entailer!. }
let ssl_var := fresh in assert_PROP(s11 = ((s1x : list Z) ++ (acc : list Z))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename t1 into t12.
forward.
assert_PROP(is_pointer_or_null((rx2 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((z : val))). { entailer!. }
assert_PROP(is_pointer_or_null((t12 : val))). { entailer!. }
forward_call ((rx2 : val), (z : val), (_alpha_5201 : sll_card), (t12 : val), (_alpha_514x : tree_card), ((s1x : list Z) ++ (acc : list Z)), (s2x : list Z)).
let ret := fresh vret in Intros ret; destruct ret as [[t2 s12] _alpha_5202].
assert_PROP(is_pointer_or_null((t2 : val))). { entailer!. }
let ssl_var := fresh in assert_PROP(s12 = ((s2x : list Z) ++ ((s1x : list Z) ++ (acc : list Z)))) as ssl_var; try rewrite ssl_var in *. { entailer!. }
try rename t2 into t22.
forward.
forward_call (tarray (Tunion _sslval noattr) 2).
Intros t3.
assert_PROP (isptr t3). { entailer!. }
forward_call (tarray (Tunion _sslval noattr) 3, x).
forward.
forward.
forward.
forward; entailer!.
Exists (t3 : val).
Exists (((([(vx2 : Z)] : list Z) ++ (s1x : list Z)) ++ (s2x : list Z)) ++ (acc : list Z)).
Exists (sll_card_1 (_alpha_5202 : sll_card) : sll_card).
ssl_entailer.
ssl_rewrite_last (unfold_sll_card_1 (_alpha_5202 : sll_card)).
Exists (vx2 : Z).
Exists ((s2x : list Z) ++ ((s1x : list Z) ++ (acc : list Z))).
Exists (t22 : val).
ssl_entailer.

}
Qed.