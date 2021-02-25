Require Import VST.floyd.proofauto.
Require Import max.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
From mathcomp Require Import seq.


Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll' (x: val) (len: Z) (lo: Z) (hi: Z) (self_card: sll_card) : mpred := match self_card with
    | sll_card_0  =>  !!(x = nullval) && !!(hi = 0) && !!(len = 0) && !!(lo = 7) && emp
    | sll_card_1 _alpha_518 => 
      EX len1 : Z,
      EX lo1 : Z,
      EX v : Z,
      EX hi1 : Z,
      EX nxt : val,
               !!(~ (x = nullval)) &&
               !!(0 <= len1) &&
               !!(0 <= v) &&
               !!(hi = (if (Z.leb hi1 v) then v else hi1)) &&
               !!(len = (1 + len1)) &&
               !!(lo = (if (Z.leb v lo1) then v else lo1)) &&
               !!(v <= 7) &&
               (data_at Tsh (tarray (Tunion _sslval noattr) 2) [inl (Vint (Int.repr v)); inr nxt] x)
               * (sll' nxt len1 lo1 hi1 _alpha_518)
end.

Fixpoint sll (x: val) (len: Z) (lo: Z) (hi: Z) (self_card: sll_card) : mpred :=
  match self_card with
  | sll_card_0  =>
    !!((x : val) = nullval) &&
    !!((hi : Z) = 0) &&
    !!((len : Z) = 0) &&
    !!((lo : Z) = 7) && emp
    | sll_card_1 _alpha_518 => 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
               !!(~ ((x : val) = nullval)) &&
               !!(0 <= (len1 : Z)) &&
               !!(0 <= (v : Z)) &&
               !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) &&
               !!((len : Z) = (1 + (len1 : Z))) &&
               !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) &&
               !!((v : Z) <= 7) &&
               (data_at Tsh (tarray (Tunion _sslval noattr) 2) [
                          (inl ((Vint (Int.repr v)) : val));
                          (inr (nxt : val))] (x : val)) *
               (sll (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_518 : sll_card))
end.

Inductive lseg2_card : Set :=
    | lseg2_card_0 : lseg2_card
    | lseg2_card_1 : lseg2_card -> lseg2_card.

Fixpoint lseg2' (x: val) (s: (list Z)) (self_card: lseg2_card) : mpred := match self_card with
    | lseg2_card_0  =>  !!(x = nullval) && !!(s = []) && emp
    | lseg2_card_1 _alpha_514 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
               !!(~ (x = nullval)) &&
               !!(s = ([v] ++ s1)) &&
               (data_at Tsh (tarray (Tunion _sslval noattr) 3)
                        [inl (Vint (Int.repr v)); inl (Vint (Int.repr (v + 1))); inr nxt] x) *
               (lseg2' nxt s1 _alpha_514)
end.

Fixpoint lseg2 (x: val) (s: (list Z)) (self_card: lseg2_card) : mpred := match self_card with
    | lseg2_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | lseg2_card_1 _alpha_514 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
               !!(~ ((x : val) = nullval)) &&
               !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) &&
               (data_at Tsh (tarray (Tunion _sslval noattr) 3)
                        [(inl ((Vint (Int.repr v)) : val));
                        (inl ((Vint (Int.repr (((v : Z) + 1)))) : val));
                        (inr (nxt : val))] (x : val)) *
               (lseg2 (nxt : val) (s1 : list Z) (_alpha_514 : lseg2_card))
end.

Inductive tree_card : Set :=
    | tree_card_0 : tree_card
    | tree_card_2 : tree_card -> tree_card -> tree_card.

Fixpoint tree' (x: val) (s: (list val)) (self_card: tree_card) : mpred := match self_card with
    | tree_card_0  =>  !!(x = nullval) && !!(s = []) && emp
    | tree_card_2 _alpha_516 _alpha_515 => 
      EX s2 : (list val),
      EX r : val,
      EX v : Z,
      EX s1 : (list val),
      EX l : val,
             !!(~ (x = nullval)) &&
             !!(s = (([(Vint (Int.repr v))] ++ s1) ++ s2)) &&
             (data_at Tsh (tarray (Tunion _sslval noattr) 3) [inl (Vint (Int.repr v)); inr l; inr r] x) *
             (tree' r s2 _alpha_516) * (tree' l s1 _alpha_515)
end.

Fixpoint tree (x: val) (s: (list Z)) (self_card: tree_card) : mpred := match self_card with
    | tree_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | tree_card_2 _alpha_516 _alpha_515 => 
      EX v : Z,
      EX s2 : (list Z),
      EX r : val,
      EX s1 : (list Z),
      EX l : val,
             !!(~ ((x : val) = nullval)) &&
             !!((s : list Z) = ((([(v : Z)] : list Z) ++ (s1 : list Z)) ++ (s2 : list Z))) &&
             (data_at Tsh (tarray (Tunion _sslval noattr) 3) [
                        (inl ((Vint (Int.repr v)) : val));
                      (inr (l : val));
                      (inr (r : val))] (x : val)) *
             (tree (r : val) (s2 : list Z) (_alpha_516 : tree_card)) *
             (tree (l : val) (s1 : list Z) (_alpha_515 : tree_card))
end.

Inductive srtl_card : Set :=
    | srtl_card_0 : srtl_card
    | srtl_card_1 : srtl_card -> srtl_card.

Fixpoint srtl' (x: val) (len: Z) (lo: Z) (hi: Z) (self_card: srtl_card) : mpred := match self_card with
    | srtl_card_0  =>  !!(x = nullval) && !!(hi = 0) && !!(len = 0) && !!(lo = 7) && emp
    | srtl_card_1 _alpha_517 => 
      EX len1 : Z,
      EX lo1 : Z,
      EX v : Z,
      EX hi1 : Z,
      EX nxt : val,
               !!(~ (x = nullval)) &&
               !!(0 <= len1) &&
               !!(0 <= v) &&
               !!(hi = (if (Z.leb hi1 v) then v else hi1)) &&
               !!(len = (1 + len1)) &&
               !!(lo = (if (Z.leb v lo1) then v else lo1)) &&
               !!(v <= 7) &&
               !!(v <= lo1) &&
               (data_at Tsh (tarray (Tunion _sslval noattr) 2) [inl (Vint (Int.repr v)); inr nxt] x) *
               (srtl' nxt len1 lo1 hi1 _alpha_517)
end.

Fixpoint srtl (x: val) (len: Z) (lo: Z) (hi: Z) (self_card: srtl_card) : mpred := match self_card with
    | srtl_card_0  =>  !!((x : val) = nullval) && !!((hi : Z) = 0) && !!((len : Z) = 0) && !!((lo : Z) = 7) && emp
    | srtl_card_1 _alpha_517 => 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
               !!(~ ((x : val) = nullval)) &&
               !!(0 <= (len1 : Z)) &&
               !!(0 <= (v : Z)) &&
               !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) &&
               !!((len : Z) = (1 + (len1 : Z))) &&
               !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) &&
               !!((v : Z) <= 7) &&
               !!((v : Z) <= (lo1 : Z)) &&
               (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) *
               (srtl (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_517 : srtl_card))
end.

Inductive lseg_card : Set :=
    | lseg_card_0 : lseg_card
    | lseg_card_1 : lseg_card -> lseg_card.

Fixpoint lseg' (x: val) (s: (list Z)) (self_card: lseg_card) : mpred := match self_card with
    | lseg_card_0  =>  !!(x = nullval) && !!(s = []) && emp
    | lseg_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val, 
               !!(~ (x = nullval)) &&
               !!(s = ([v] ++ s1)) &&
               (data_at Tsh (tarray (Tunion _sslval noattr) 2) [inl (Vint (Int.repr v)); inr nxt] x) *
               (lseg' nxt s1 _alpha_513)
end.

Fixpoint lseg (x: val) (s: (list Z)) (self_card: lseg_card) : mpred := match self_card with
    | lseg_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | lseg_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
               !!(~ ((x : val) = nullval)) &&
               !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) &&
               (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) *
               (lseg (nxt : val) (s1 : list Z) (_alpha_513 : lseg_card))
end.

Definition max_spec :=
  DECLARE _max
   WITH r: val, x: val, y: val
   PRE [ (tptr (Tunion _sslval noattr)), tint, tint ]
   PROP( is_pointer_or_null(r); ssl_is_valid_int(x); ssl_is_valid_int(y) )
   PARAMS(r; x; y)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inl (Vint (Int.repr 0))] r))
   POST[ tvoid ]
   EX m: Z,
   PROP( ((force_signed_int x) <= m); ((force_signed_int y) <= m) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inl (Vint (Int.repr m))] r)).

Definition max_spec2 :=
  DECLARE _max
   WITH r: val, x: val, y: val
   PRE [ (tptr (Tunion _sslval noattr)), tint, tint ]
   PROP( is_pointer_or_null(r); ssl_is_valid_int(x); ssl_is_valid_int(y) )
   PARAMS(r; x; y)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inl ((Vint (Int.repr 0)) : val))] (r : val)))
   POST[ tvoid ]
   EX m: Z,
   PROP( ((force_signed_int (x : val)) <= (m : Z)); ((force_signed_int (y : val)) <= (m : Z)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inl ((Vint (Int.repr m)) : val))] (r : val))).

Lemma sll_x_valid_pointerP x len lo hi self_card: sll x len lo hi self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x len lo hi self_card :
  sll x len lo hi self_card|-- !!((((x = nullval)) -> (self_card = sll_card_0))/\(((~ (x = nullval))) -> (exists _alpha_518, self_card = sll_card_1 _alpha_518))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve sll_local_factsP : saturate_local.
Lemma lseg2_x_valid_pointerP x s self_card: lseg2 x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve lseg2_x_valid_pointerP : valid_pointer.
Lemma lseg2_local_factsP x s self_card :
  lseg2 x s self_card|-- !!((((x = nullval)) -> (self_card = lseg2_card_0))/\(((~ (x = nullval))) -> (exists _alpha_514, self_card = lseg2_card_1 _alpha_514))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve lseg2_local_factsP : saturate_local.
Lemma tree_x_valid_pointerP x s self_card: tree x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve tree_x_valid_pointerP : valid_pointer.
Lemma tree_local_factsP x s self_card :
  tree x s self_card|-- !!((((x = nullval)) -> (self_card = tree_card_0))/\(((~ (x = nullval))) -> (exists _alpha_516 _alpha_515, self_card = tree_card_2 _alpha_516 _alpha_515))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve tree_local_factsP : saturate_local.
Lemma srtl_x_valid_pointerP x len lo hi self_card: srtl x len lo hi self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve srtl_x_valid_pointerP : valid_pointer.
Lemma srtl_local_factsP x len lo hi self_card :
  srtl x len lo hi self_card|-- !!((((x = nullval)) -> (self_card = srtl_card_0))/\(((~ (x = nullval))) -> (exists _alpha_517, self_card = srtl_card_1 _alpha_517))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve srtl_local_factsP : saturate_local.
Lemma lseg_x_valid_pointerP x s self_card: lseg x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve lseg_x_valid_pointerP : valid_pointer.
Lemma lseg_local_factsP x s self_card :
  lseg x s self_card|-- !!((((x = nullval)) -> (self_card = lseg_card_0))/\(((~ (x = nullval))) -> (exists _alpha_513, self_card = lseg_card_1 _alpha_513))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve lseg_local_factsP : saturate_local.
Definition Gprog : funspecs :=
  ltac:(with_library prog [max_spec]).

Lemma body_max : semax_body Vprog Gprog f_max max_spec2.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
forward_if.
 - {
forward.
forward; entailer!.
Exists (x).
entailer!.

}
 - {
assert_PROP (isptr r). { entailer!. }
forward.
forward; entailer!.
Exists (y).
entailer!.

}
Qed.
