
Require Import VST.floyd.proofauto.
Require Import common.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.



Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: val) (s: (list Z)) (self_card: sll_card) {struct self_card} : mpred := match self_card with
    | sll_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | sll_card_1 _alpha_543 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_543 : sll_card))
end.

Inductive treeN_card : Set :=
    | treeN_card_0 : treeN_card
    | treeN_card_2 : treeN_card -> treeN_card -> treeN_card.

Fixpoint treeN (x: val) (n: Z) (self_card: treeN_card) {struct self_card} : mpred := match self_card with
    | treeN_card_0  =>  !!((x : val) = nullval) && !!((n : Z) = 0) && emp
    | treeN_card_2 _alpha_542 _alpha_541 => 
      EX n1 : Z,
      EX v : val,
      EX r : val,
      EX n2 : Z,
      EX l : val,
 !!(Int.min_signed <= n1 <= Int.max_signed) && !!(is_pointer_or_null v) && !!(is_pointer_or_null r) && !!(Int.min_signed <= n2 <= Int.max_signed) && !!(is_pointer_or_null l) && !!(~ ((x : val) = nullval)) && !!(0 <= (n1 : Z)) && !!(0 <= (n2 : Z)) && !!((n : Z) = ((1 + (n1 : Z)) + (n2 : Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inr (v : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (treeN (l : val) (n1 : Z) (_alpha_541 : treeN_card)) * (treeN (r : val) (n2 : Z) (_alpha_542 : treeN_card))
end.

Inductive tree_card : Set :=
    | tree_card_0 : tree_card
    | tree_card_2 : tree_card -> tree_card -> tree_card.

Fixpoint tree (x: val) (s: (list Z)) (self_card: tree_card) {struct self_card} : mpred := match self_card with
    | tree_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | tree_card_2 _alpha_540 _alpha_539 => 
      EX v : Z,
      EX s2 : (list Z),
      EX r : val,
      EX s1 : (list Z),
      EX l : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null r) && !!(is_pointer_or_null l) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = ((([(v : Z)] : list Z) ++ (s1 : list Z)) ++ (s2 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (tree (l : val) (s1 : list Z) (_alpha_539 : tree_card)) * (tree (r : val) (s2 : list Z) (_alpha_540 : tree_card))
end.



Lemma sll_x_valid_pointerP x s self_card: sll x s self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x s self_card :
  sll x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = sll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_543, self_card = sll_card_1 _alpha_543))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve sll_local_factsP : saturate_local.
Lemma unfold_sll_card_0  (x: val) (s: (list Z)) : sll x s (sll_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_sll_card_1 (_alpha_543 : sll_card) (x: val) (s: (list Z)) : sll x s (sll_card_1 _alpha_543) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_543 : sll_card)). Proof. auto. Qed.
Lemma treeN_x_valid_pointerP x n self_card: treeN x n self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve treeN_x_valid_pointerP : valid_pointer.
Lemma treeN_local_factsP x n self_card :
  treeN x n self_card|-- !!(((((x : val) = nullval)) -> (self_card = treeN_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_542 _alpha_541, self_card = treeN_card_2 _alpha_542 _alpha_541))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve treeN_local_factsP : saturate_local.
Lemma unfold_treeN_card_0  (x: val) (n: Z) : treeN x n (treeN_card_0 ) =  !!((x : val) = nullval) && !!((n : Z) = 0) && emp. Proof. auto. Qed.
Lemma unfold_treeN_card_2 (_alpha_542 : treeN_card) (_alpha_541 : treeN_card) (x: val) (n: Z) : treeN x n (treeN_card_2 _alpha_542 _alpha_541) = 
      EX n1 : Z,
      EX v : val,
      EX r : val,
      EX n2 : Z,
      EX l : val,
 !!(Int.min_signed <= n1 <= Int.max_signed) && !!(is_pointer_or_null v) && !!(is_pointer_or_null r) && !!(Int.min_signed <= n2 <= Int.max_signed) && !!(is_pointer_or_null l) && !!(~ ((x : val) = nullval)) && !!(0 <= (n1 : Z)) && !!(0 <= (n2 : Z)) && !!((n : Z) = ((1 + (n1 : Z)) + (n2 : Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inr (v : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (treeN (l : val) (n1 : Z) (_alpha_541 : treeN_card)) * (treeN (r : val) (n2 : Z) (_alpha_542 : treeN_card)). Proof. auto. Qed.
Lemma tree_x_valid_pointerP x s self_card: tree x s self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve tree_x_valid_pointerP : valid_pointer.
Lemma tree_local_factsP x s self_card :
  tree x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = tree_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_540 _alpha_539, self_card = tree_card_2 _alpha_540 _alpha_539))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve tree_local_factsP : saturate_local.
Lemma unfold_tree_card_0  (x: val) (s: (list Z)) : tree x s (tree_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_tree_card_2 (_alpha_540 : tree_card) (_alpha_539 : tree_card) (x: val) (s: (list Z)) : tree x s (tree_card_2 _alpha_540 _alpha_539) = 
      EX v : Z,
      EX s2 : (list Z),
      EX r : val,
      EX s1 : (list Z),
      EX l : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null r) && !!(is_pointer_or_null l) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = ((([(v : Z)] : list Z) ++ (s1 : list Z)) ++ (s2 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (tree (l : val) (s1 : list Z) (_alpha_539 : tree_card)) * (tree (r : val) (s2 : list Z) (_alpha_540 : tree_card)). Proof. auto. Qed.