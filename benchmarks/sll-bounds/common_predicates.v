
Require Import VST.floyd.proofauto.
Require Import common.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.



Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: val) (len: Z) (lo: Z) (hi: Z) (self_card: sll_card) {struct self_card} : mpred := match self_card with
    | sll_card_0  =>  !!((x : val) = nullval) && !!((hi : Z) = 0) && !!((len : Z) = 0) && !!((lo : Z) = 7) && emp
    | sll_card_1 _alpha_513 => 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(Int.min_signed <= len1 <= Int.max_signed) && !!(Int.min_signed <= hi1 <= Int.max_signed) && !!(Int.min_signed <= lo1 <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!(0 <= (len1 : Z)) && !!(0 <= (v : Z)) && !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) && !!((len : Z) = (1 + (len1 : Z))) && !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) && !!((v : Z) <= 7) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_513 : sll_card))
end.



Lemma sll_x_valid_pointerP x len lo hi self_card: sll x len lo hi self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x len lo hi self_card :
  sll x len lo hi self_card|-- !!(((((x : val) = nullval)) -> (self_card = sll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_513, self_card = sll_card_1 _alpha_513))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve sll_local_factsP : saturate_local.
Lemma unfold_sll_card_0  (x: val) (len: Z) (lo: Z) (hi: Z) : sll x len lo hi (sll_card_0 ) =  !!((x : val) = nullval) && !!((hi : Z) = 0) && !!((len : Z) = 0) && !!((lo : Z) = 7) && emp. Proof. auto. Qed.
Lemma unfold_sll_card_1 (_alpha_513 : sll_card) (x: val) (len: Z) (lo: Z) (hi: Z) : sll x len lo hi (sll_card_1 _alpha_513) = 
      EX v : Z,
      EX nxt : val,
      EX len1 : Z,
      EX hi1 : Z,
      EX lo1 : Z,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(Int.min_signed <= len1 <= Int.max_signed) && !!(Int.min_signed <= hi1 <= Int.max_signed) && !!(Int.min_signed <= lo1 <= Int.max_signed) && !!(~ ((x : val) = nullval)) && !!(0 <= (len1 : Z)) && !!(0 <= (v : Z)) && !!((hi : Z) = (if (Z.leb (hi1 : Z) (v : Z)) then (v : Z) else (hi1 : Z))) && !!((len : Z) = (1 + (len1 : Z))) && !!((lo : Z) = (if (Z.leb (v : Z) (lo1 : Z)) then (v : Z) else (lo1 : Z))) && !!((v : Z) <= 7) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (len1 : Z) (lo1 : Z) (hi1 : Z) (_alpha_513 : sll_card)). Proof. auto. Qed.