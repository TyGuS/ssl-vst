
Require Import VST.floyd.proofauto.
Require Import common.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.



Inductive dll_card : Set :=
    | dll_card_0 : dll_card
    | dll_card_1 : dll_card -> dll_card.

Fixpoint dll (x: val) (z: val) (s: (list Z)) (self_card: dll_card) {struct self_card} : mpred := match self_card with
    | dll_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | dll_card_1 _alpha_533 => 
      EX v : Z,
      EX s1 : (list Z),
      EX w : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null w) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (w : val)); (inr (z : val))] (x : val)) * (dll (w : val) (x : val) (s1 : list Z) (_alpha_533 : dll_card))
end.



Lemma dll_x_valid_pointerP x z s self_card: dll x z s self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve dll_x_valid_pointerP : valid_pointer.
Lemma dll_local_factsP x z s self_card :
  dll x z s self_card|-- !!(((((x : val) = nullval)) -> (self_card = dll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_533, self_card = dll_card_1 _alpha_533))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve dll_local_factsP : saturate_local.
Lemma unfold_dll_card_0  (x: val) (z: val) (s: (list Z)) : dll x z s (dll_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_dll_card_1 (_alpha_533 : dll_card) (x: val) (z: val) (s: (list Z)) : dll x z s (dll_card_1 _alpha_533) = 
      EX v : Z,
      EX s1 : (list Z),
      EX w : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null w) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (w : val)); (inr (z : val))] (x : val)) * (dll (w : val) (x : val) (s1 : list Z) (_alpha_533 : dll_card)). Proof. auto. Qed.