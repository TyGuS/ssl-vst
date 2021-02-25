
Require Import VST.floyd.proofauto.
Require Import flatten.
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

Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: val) (len: Z) (lo: Z) (hi: Z) (self_card: sll_card) {struct self_card} : mpred := match self_card with
    | sll_card_0  =>  !!((x : val) = nullval) && !!((hi : Z) = 0) && !!((len : Z) = 0) && !!((lo : Z) = 7) && emp
    | sll_card_1 _alpha_518 => 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
 !!(~ ((x : val) = nullval)) && !!(0 <= (len1 : Z)) && !!(0 <= (v : Z)) && !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) && !!((len : Z) = (1 + (len1 : Z))) && !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) && !!((v : Z) <= 7) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_518 : sll_card))
end.

Inductive lseg2_card : Set :=
    | lseg2_card_0 : lseg2_card
    | lseg2_card_1 : lseg2_card -> lseg2_card.

Fixpoint lseg2 (x: val) (s: (list Z)) (self_card: lseg2_card) {struct self_card} : mpred := match self_card with
    | lseg2_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | lseg2_card_1 _alpha_514 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inl ((Vint (Int.repr (((v : Z) + 1)))) : val)); (inr (nxt : val))] (x : val)) * (lseg2 (nxt : val) (s1 : list Z) (_alpha_514 : lseg2_card))
end.

Inductive tree_card : Set :=
    | tree_card_0 : tree_card
    | tree_card_2 : tree_card -> tree_card -> tree_card.

Fixpoint tree (x: val) (s: (list Z)) (self_card: tree_card) {struct self_card} : mpred := match self_card with
    | tree_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | tree_card_2 _alpha_516 _alpha_515 => 
      EX v : Z,
      EX s2 : (list Z),
      EX r : val,
      EX s1 : (list Z),
      EX l : val,
 !!(~ ((x : val) = nullval)) && !!((s : list Z) = ((([(v : Z)] : list Z) ++ (s1 : list Z)) ++ (s2 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (tree (r : val) (s2 : list Z) (_alpha_516 : tree_card)) * (tree (l : val) (s1 : list Z) (_alpha_515 : tree_card))
end.

Inductive account_card : Set :=
    | account_card_0 : account_card.

Fixpoint account (x: val) (id: Z) (bal: Z) (self_card: account_card) {struct self_card} : mpred := match self_card with
    | account_card_0  =>  !!(is_true true) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr id)) : val)); (inl ((Vint (Int.repr bal)) : val))] (x : val))
end.

Inductive srtl_card : Set :=
    | srtl_card_0 : srtl_card
    | srtl_card_1 : srtl_card -> srtl_card.

Fixpoint srtl (x: val) (len: Z) (lo: Z) (hi: Z) (self_card: srtl_card) {struct self_card} : mpred := match self_card with
    | srtl_card_0  =>  !!((x : val) = nullval) && !!((hi : Z) = 0) && !!((len : Z) = 0) && !!((lo : Z) = 7) && emp
    | srtl_card_1 _alpha_517 => 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
 !!(~ ((x : val) = nullval)) && !!(0 <= (len1 : Z)) && !!(0 <= (v : Z)) && !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) && !!((len : Z) = (1 + (len1 : Z))) && !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) && !!((v : Z) <= 7) && !!((v : Z) <= (lo1 : Z)) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (srtl (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_517 : srtl_card))
end.

Inductive lseg_card : Set :=
    | lseg_card_0 : lseg_card
    | lseg_card_1 : lseg_card -> lseg_card.

Fixpoint lseg (x: val) (s: (list Z)) (self_card: lseg_card) {struct self_card} : mpred := match self_card with
    | lseg_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | lseg_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (lseg (nxt : val) (s1 : list Z) (_alpha_513 : lseg_card))
end.

Definition lseg_append_spec :=
  DECLARE _lseg_append
   WITH x1: val, ret: val, x2: val, s2: (list Z), _alpha_520: lseg_card, _alpha_519: lseg_card, s1: (list Z)
   PRE [ (tptr (Tunion _sslval noattr)), (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((x1 : val)); is_pointer_or_null((ret : val)); is_pointer_or_null((x2 : val)) )
   PARAMS(x1; ret)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x2 : val))] (ret : val)); (lseg (x2 : val) (s2 : list Z) (_alpha_520 : lseg_card)); (lseg (x1 : val) (s1 : list Z) (_alpha_519 : lseg_card)))
   POST[ tvoid ]
   EX y: val,
   EX s: (list Z),
   EX _alpha_521: lseg_card,
   PROP( ((s : list Z) = ((s1 : list Z) ++ (s2 : list Z))) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (ret : val)); (lseg (y : val) (s : list Z) (_alpha_521 : lseg_card))).

Definition flatten_spec :=
  DECLARE _flatten
   WITH z: val, x: val, s: (list Z), _alpha_522: tree_card
   PRE [ (tptr (Tunion _sslval noattr)) ]
   PROP( is_pointer_or_null((z : val)); is_pointer_or_null((x : val)) )
   PARAMS(z)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (x : val))] (z : val)); (tree (x : val) (s : list Z) (_alpha_522 : tree_card)))
   POST[ tvoid ]
   EX y: val,
   EX _alpha_523: lseg_card,
   PROP(  )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (y : val))] (z : val)); (lseg (y : val) (s : list Z) (_alpha_523 : lseg_card))).

Lemma sll_x_valid_pointerP x len lo hi self_card: sll x len lo hi self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x len lo hi self_card :
  sll x len lo hi self_card|-- !!(((((x : val) = nullval)) -> (self_card = sll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_518, self_card = sll_card_1 _alpha_518))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve sll_local_factsP : saturate_local.
Lemma unfold_sll_card_0  (x: val) (len: Z) (lo: Z) (hi: Z) : sll x len lo hi (sll_card_0 ) =  !!((x : val) = nullval) && !!((hi : Z) = 0) && !!((len : Z) = 0) && !!((lo : Z) = 7) && emp. Proof. auto. Qed.
Lemma unfold_sll_card_1 (_alpha_518 : sll_card) (x: val) (len: Z) (lo: Z) (hi: Z) : sll x len lo hi (sll_card_1 _alpha_518) = 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
 !!(~ ((x : val) = nullval)) && !!(0 <= (len1 : Z)) && !!(0 <= (v : Z)) && !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) && !!((len : Z) = (1 + (len1 : Z))) && !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) && !!((v : Z) <= 7) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_518 : sll_card)). Proof. auto. Qed.
Lemma lseg2_x_valid_pointerP x s self_card: lseg2 x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve lseg2_x_valid_pointerP : valid_pointer.
Lemma lseg2_local_factsP x s self_card :
  lseg2 x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = lseg2_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_514, self_card = lseg2_card_1 _alpha_514))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve lseg2_local_factsP : saturate_local.
Lemma unfold_lseg2_card_0  (x: val) (s: (list Z)) : lseg2 x s (lseg2_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_lseg2_card_1 (_alpha_514 : lseg2_card) (x: val) (s: (list Z)) : lseg2 x s (lseg2_card_1 _alpha_514) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inl ((Vint (Int.repr (((v : Z) + 1)))) : val)); (inr (nxt : val))] (x : val)) * (lseg2 (nxt : val) (s1 : list Z) (_alpha_514 : lseg2_card)). Proof. auto. Qed.
Lemma tree_x_valid_pointerP x s self_card: tree x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve tree_x_valid_pointerP : valid_pointer.
Lemma tree_local_factsP x s self_card :
  tree x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = tree_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_516 _alpha_515, self_card = tree_card_2 _alpha_516 _alpha_515))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve tree_local_factsP : saturate_local.
Lemma unfold_tree_card_0  (x: val) (s: (list Z)) : tree x s (tree_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_tree_card_2 (_alpha_516 : tree_card) (_alpha_515 : tree_card) (x: val) (s: (list Z)) : tree x s (tree_card_2 _alpha_516 _alpha_515) = 
      EX v : Z,
      EX s2 : (list Z),
      EX r : val,
      EX s1 : (list Z),
      EX l : val,
 !!(~ ((x : val) = nullval)) && !!((s : list Z) = ((([(v : Z)] : list Z) ++ (s1 : list Z)) ++ (s2 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (l : val)); (inr (r : val))] (x : val)) * (tree (r : val) (s2 : list Z) (_alpha_516 : tree_card)) * (tree (l : val) (s1 : list Z) (_alpha_515 : tree_card)). Proof. auto. Qed.
Lemma account_x_valid_pointerP x id bal self_card: account x id bal self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve account_x_valid_pointerP : valid_pointer.
Lemma account_local_factsP x id bal self_card :
  account x id bal self_card|-- !!((((is_true true)) -> (self_card = account_card_0))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve account_local_factsP : saturate_local.
Lemma unfold_account_card_0  (x: val) (id: Z) (bal: Z) : account x id bal (account_card_0 ) =  !!(is_true true) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr id)) : val)); (inl ((Vint (Int.repr bal)) : val))] (x : val)). Proof. auto. Qed.
Lemma srtl_x_valid_pointerP x len lo hi self_card: srtl x len lo hi self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve srtl_x_valid_pointerP : valid_pointer.
Lemma srtl_local_factsP x len lo hi self_card :
  srtl x len lo hi self_card|-- !!(((((x : val) = nullval)) -> (self_card = srtl_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_517, self_card = srtl_card_1 _alpha_517))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve srtl_local_factsP : saturate_local.
Lemma unfold_srtl_card_0  (x: val) (len: Z) (lo: Z) (hi: Z) : srtl x len lo hi (srtl_card_0 ) =  !!((x : val) = nullval) && !!((hi : Z) = 0) && !!((len : Z) = 0) && !!((lo : Z) = 7) && emp. Proof. auto. Qed.
Lemma unfold_srtl_card_1 (_alpha_517 : srtl_card) (x: val) (len: Z) (lo: Z) (hi: Z) : srtl x len lo hi (srtl_card_1 _alpha_517) = 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
 !!(~ ((x : val) = nullval)) && !!(0 <= (len1 : Z)) && !!(0 <= (v : Z)) && !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) && !!((len : Z) = (1 + (len1 : Z))) && !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) && !!((v : Z) <= 7) && !!((v : Z) <= (lo1 : Z)) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (srtl (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_517 : srtl_card)). Proof. auto. Qed.
Lemma lseg_x_valid_pointerP x s self_card: lseg x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve lseg_x_valid_pointerP : valid_pointer.
Lemma lseg_local_factsP x s self_card :
  lseg x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = lseg_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_513, self_card = lseg_card_1 _alpha_513))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve lseg_local_factsP : saturate_local.
Lemma unfold_lseg_card_0  (x: val) (s: (list Z)) : lseg x s (lseg_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_lseg_card_1 (_alpha_513 : lseg_card) (x: val) (s: (list Z)) : lseg x s (lseg_card_1 _alpha_513) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (lseg (nxt : val) (s1 : list Z) (_alpha_513 : lseg_card)). Proof. auto. Qed.
Definition Gprog : funspecs :=
  ltac:(with_library prog [flatten_spec; free_spec; malloc_spec;lseg_append_spec]).

Lemma body_flatten : semax_body Vprog Gprog f_flatten flatten_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr z). { entailer!. }
try rename x into x2.
forward.
forward_if.

 - {
assert_PROP (_alpha_522 = tree_card_0) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert .
assert_PROP (((x2 : val) = nullval)). { entailer!. }
let ssl_var := fresh in assert_PROP(s = ([] : list Z)) as ssl_var; try rewrite ssl_var in *. { entailer!. }
forward; entailer!.
Exists nullval.
Exists (lseg_card_0  : lseg_card).
try entailer!.
ssl_rewrite_last (unfold_lseg_card_0 ).
try entailer!.

}
 - {
assert_PROP (exists _alpha_516 _alpha_515, _alpha_522 = tree_card_2 _alpha_516 _alpha_515) as ssl_card_assert. { entailer!; ssl_dispatch_card. }
ssl_card tree ssl_card_assert _alpha_516x2 _alpha_515x2.
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
forward_call ((z : val), (lx22 : val), (s1x2 : list Z), (_alpha_515x2 : tree_card)).
let ret := fresh vret in Intros ret; destruct ret as [y1 _alpha_5231].
try rename y1 into y12.
forward.
forward.
assert_PROP(is_pointer_or_null((z : val))). { entailer!. }
assert_PROP(is_pointer_or_null((rx22 : val))). { entailer!. }
forward_call ((z : val), (rx22 : val), (s2x2 : list Z), (_alpha_516x2 : tree_card)).
let ret := fresh vret in Intros ret; destruct ret as [y2 _alpha_5232].
try rename y2 into y22.
forward.
assert_PROP(is_pointer_or_null((y12 : val))). { entailer!. }
assert_PROP(is_pointer_or_null((z : val))). { entailer!. }
assert_PROP(is_pointer_or_null((y22 : val))). { entailer!. }
forward_call ((y12 : val), (z : val), (y22 : val), (s2x2 : list Z), (_alpha_5232 : lseg_card), (_alpha_5231 : lseg_card), (s1x2 : list Z)).
try entailer!.
let ret := fresh vret in Intros ret; destruct ret as [[y3 s3] _alpha_521].
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
Exists (lseg_card_1 (_alpha_521 : lseg_card) : lseg_card).
try entailer!.
ssl_rewrite_last (unfold_lseg_card_1 (_alpha_521 : lseg_card)).
Exists (vx22 : Z).
Exists ((s1x2 : list Z) ++ (s2x2 : list Z)).
Exists (y32 : val).
try entailer!.

}
Qed.