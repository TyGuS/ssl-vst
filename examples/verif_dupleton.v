Require Import VST.floyd.proofauto.
Require Import dll_dupleton.
From SSL_VST Require Import core.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Notation "a |~> b" :=
  (data_at Tsh (tarray (Tunion _sslval noattr) 1) [b] a) (at level 1).
Notation "a '|~>' '[' b ';' c ']'" :=
  (data_at Tsh (tarray (Tunion _sslval noattr) 2) [b; c] a) (at level 1).
Notation "'$(int)(' a ')'" := (inl (Vint (Int.repr a))).
Notation "'$(ptr)(' a ')'" := (inr a).
Notation "'int[' n ']'" := (tarray (Tunion _sslval noattr) n).

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

Fixpoint dll (x: val) (z: val) (s: (list val)) (self_card: dll_card) : mpred := match self_card with
    | dll_card_0  =>  !!(x = nullval) && !!(s = []) && emp
    | dll_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list val),
      EX w : val,
 !!(~ (x = nullval)) && !!(s = ([(Vint (Int.repr v))] ++ s1)) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [inl (Vint (Int.repr v)); inr w; inr z] x) * (dll w x s1 _alpha_513)
end.


Definition dll_dupleton_spec :=
  DECLARE _dll_dupleton
   WITH x: val, y: val, r: val, a: val
   PRE [ tint, tint, (tptr (Tunion _sslval noattr)) ]
   PROP( ssl_is_valid_int(x); ssl_is_valid_int(y); is_pointer_or_null(r); is_pointer_or_null(a) )
   PARAMS(x; y; r)
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inr a] r))
   POST[ tvoid ]
   EX _alpha_515: dll_card,
   EX elems: (list val),
   EX z: val,
   PROP( (elems = [x; y]) )
   LOCAL()
   SEP ((data_at Tsh (tarray (Tunion _sslval noattr) 1) [inr z] r); (dll z nullval elems _alpha_515)).


Lemma dll_x_valid_pointerP x z s self_card: dll x z s self_card |-- valid_pointer x.
Proof.
  case self_card.
  simpl; entailer!.
  simpl; intro _card; Intros _card' elems z'. 
  entailer!.
Qed.
Hint Resolve dll_x_valid_pointerP : valid_pointer.

Lemma dll_local_factsP x z s self_card :
  dll x z s self_card |--
      !!((((x = nullval)) -> (self_card = dll_card_0)) /\
         (((~ (x = nullval))) -> (exists _alpha_518, self_card = dll_card_1 _alpha_518)) /\
         (is_pointer_or_null x)).
Proof.
  case self_card. simpl; entailer!.
  intro d; simpl; Intros _alpha_515 elems z'.
  entailer!.
  exists d; auto.
Qed.
Hint Resolve dll_local_factsP : saturate_local.

Definition Gprog : funspecs :=
  ltac:(with_library prog [dll_dupleton_spec; malloc_spec]).

Lemma body_dll_dupleton : semax_body Vprog Gprog f_dll_dupleton dll_dupleton_spec.
Proof.
  start_function.
  ssl_open_context.
  forward_call (tarray (Tunion _sslval noattr) 3 ).
  Intro z2.
  forward_call (tarray (Tunion _sslval noattr) 3 ).
  Intro z3.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward; entailer!.
  simpl.
  Exists (dll_card_1 (dll_card_1 dll_card_0)).
  Exists [Vint (Int.repr x); Vint (Int.repr y)].
  Exists z2.
  simpl (dll _ _ _ (dll_card_1 (dll_card_1 dll_card_0))).
  Exists x [Vint (Int.repr y)] z3.
  Exists y ([]: list val) nullval.
  entailer!.
Qed.
