
Require Import VST.floyd.proofauto.
Require Import dll_dupleton.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

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

Inductive dll_card : Set :=
    | dll_card_0 : dll_card
    | dll_card_1 : dll_card -> dll_card.

Fixpoint dll (x: val) (z: val) (s: (list Z)) (self_card: dll_card) {struct self_card} : mpred := match self_card with
    | dll_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | dll_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list Z),
      EX w : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null w) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (w : val)); (inr (z : val))] (x : val)) * (dll (w : val) (x : val) (s1 : list Z) (_alpha_513 : dll_card))
end.

Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: val) (s: (list Z)) (self_card: sll_card) {struct self_card} : mpred := match self_card with
    | sll_card_0  =>  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp
    | sll_card_1 _alpha_514 => 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_514 : sll_card))
end.


Definition dll_dupleton_spec :=
  DECLARE _dll_dupleton
   WITH x: val, y: val, r: val, a: val
   PRE [ tint, tint, (tptr (Tunion _sslval noattr)) ]
   PROP( ssl_is_valid_int((x : val)); ssl_is_valid_int((y : val)); is_pointer_or_null((r : val)); is_pointer_or_null((a : val)) )
   PARAMS(x; y; r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (a : val))] (r : val)))
   POST[ tvoid ]
   EX _alpha_515: dll_card,
   EX elems: (list Z),
   EX z: val,
   PROP( ((elems : list Z) = ([(force_signed_int (x : val)); (force_signed_int (y : val))] : list Z)); is_pointer_or_null((z : val)) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [(inr (z : val))] (r : val)); (dll (z : val) nullval (elems : list Z) (_alpha_515 : dll_card))).

Lemma dll_x_valid_pointerP x z s self_card: dll x z s self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve dll_x_valid_pointerP : valid_pointer.
Lemma dll_local_factsP x z s self_card :
  dll x z s self_card|-- !!(((((x : val) = nullval)) -> (self_card = dll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_513, self_card = dll_card_1 _alpha_513))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve dll_local_factsP : saturate_local.
Lemma unfold_dll_card_0  (x: val) (z: val) (s: (list Z)) : dll x z s (dll_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_dll_card_1 (_alpha_513 : dll_card) (x: val) (z: val) (s: (list Z)) : dll x z s (dll_card_1 _alpha_513) = 
      EX v : Z,
      EX s1 : (list Z),
      EX w : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null w) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [(inl ((Vint (Int.repr v)) : val)); (inr (w : val)); (inr (z : val))] (x : val)) * (dll (w : val) (x : val) (s1 : list Z) (_alpha_513 : dll_card)). Proof. auto. Qed.
Lemma sll_x_valid_pointerP x s self_card: sll x s self_card |-- valid_pointer x. Proof. destruct self_card; simpl; entailer;  entailer!; eauto. Qed.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x s self_card :
  sll x s self_card|-- !!(((((x : val) = nullval)) -> (self_card = sll_card_0))/\(((~ ((x : val) = nullval))) -> (exists _alpha_514, self_card = sll_card_1 _alpha_514))/\is_pointer_or_null((x : val))).
 Proof.  destruct self_card;  simpl; entailer; saturate_local; apply prop_right; eauto. Qed.
Hint Resolve sll_local_factsP : saturate_local.
Lemma unfold_sll_card_0  (x: val) (s: (list Z)) : sll x s (sll_card_0 ) =  !!((x : val) = nullval) && !!((s : list Z) = ([] : list Z)) && emp. Proof. auto. Qed.
Lemma unfold_sll_card_1 (_alpha_514 : sll_card) (x: val) (s: (list Z)) : sll x s (sll_card_1 _alpha_514) = 
      EX v : Z,
      EX s1 : (list Z),
      EX nxt : val,
 !!(Int.min_signed <= v <= Int.max_signed) && !!(is_pointer_or_null nxt) && !!(~ ((x : val) = nullval)) && !!((s : list Z) = (([(v : Z)] : list Z) ++ (s1 : list Z))) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [(inl ((Vint (Int.repr v)) : val)); (inr (nxt : val))] (x : val)) * (sll (nxt : val) (s1 : list Z) (_alpha_514 : sll_card)). Proof. auto. Qed.
Definition Gprog : funspecs :=
  ltac:(with_library prog [dll_dupleton_spec; malloc_spec]).

Lemma body_dll_dupleton : semax_body Vprog Gprog f_dll_dupleton dll_dupleton_spec.
Proof.
start_function.
ssl_open_context.
assert_PROP (isptr r). { entailer!. }
try rename a into a2.
forward.
forward_call (tarray (Tunion _sslval noattr) 3).
Intros z2.
assert_PROP (isptr z2). { entailer!. }
forward_call (tarray (Tunion _sslval noattr) 3).
Intros wz2.
assert_PROP (isptr wz2). { entailer!. }
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward; entailer!.
Exists (dll_card_1 (dll_card_1 (dll_card_0  : dll_card) : dll_card) : dll_card).
Exists ([(x : Z); (y : Z)] : list Z).
Exists (z2 : val).
ssl_entailer.
rewrite (unfold_dll_card_1 (dll_card_1 (dll_card_0  : dll_card) : dll_card)) at 1.
Exists (x : Z).
Exists (([(y : Z)] : list Z) ++ ([] : list Z)).
Exists (wz2 : val).
ssl_entailer.
rewrite (unfold_dll_card_1 (dll_card_0  : dll_card)) at 1.
Exists (y : Z).
Exists ([] : list Z).
Exists nullval.
ssl_entailer.
rewrite (unfold_dll_card_0 ) at 1.
ssl_entailer.

Qed.