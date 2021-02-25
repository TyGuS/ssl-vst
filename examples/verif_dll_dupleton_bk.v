
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

Fixpoint dll (x: val) (z: val) (s: (list val)) (self_card: dll_card) : mpred := match self_card with
    | dll_card_0  =>  !!(x = nullval) && !!(s = []) && emp
    | dll_card_1 _alpha_513 => 
      EX v : Z,
      EX s1 : (list val),
      EX w : val,
 !!(~ (x = nullval)) && !!(s = ([(Vint (Int.repr v))] ++ s1)) && (data_at Tsh (tarray (Tunion _sslval noattr) 3) [inl (Vint (Int.repr v)); inr w; inr z] x) * (dll w x s1 _alpha_513)
end.

Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: val) (s: (list val)) (self_card: sll_card) : mpred := match self_card with
    | sll_card_0  =>  !!(x = nullval) && !!(s = []) && emp
    | sll_card_1 _alpha_514 => 
      EX v : Z,
      EX s1 : (list val),
      EX nxt : val,
 !!(~ (x = nullval)) && !!(s = ([(Vint (Int.repr v))] ++ s1)) && (data_at Tsh (tarray (Tunion _sslval noattr) 2) [inl (Vint (Int.repr v)); inr nxt] x) * (sll nxt s1 _alpha_514)
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

Lemma dll_x_valid_pointerP x z s self_card: dll x z s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve dll_x_valid_pointerP : valid_pointer.
Lemma dll_z_valid_pointerP x z s self_card: dll x z s self_card |-- valid_pointer z. Proof. Admitted.
Hint Resolve dll_z_valid_pointerP : valid_pointer.
Lemma dll_local_factsP x z s self_card :
  dll x z s self_card|-- !!((((x = nullval)) -> (self_card = dll_card_0))/\(((~ (x = nullval))) -> (exists _alpha_513, self_card = dll_card_1 _alpha_513))/\(is_pointer_or_null x)/\(is_pointer_or_null z)). Proof. Admitted.
Hint Resolve dll_local_factsP : saturate_local.
Lemma sll_x_valid_pointerP x s self_card: sll x s self_card |-- valid_pointer x. Proof. Admitted.
Hint Resolve sll_x_valid_pointerP : valid_pointer.
Lemma sll_local_factsP x s self_card :
  sll x s self_card|-- !!((((x = nullval)) -> (self_card = sll_card_0))/\(((~ (x = nullval))) -> (exists _alpha_514, self_card = sll_card_1 _alpha_514))/\(is_pointer_or_null x)). Proof. Admitted.
Hint Resolve sll_local_factsP : saturate_local.
Definition Gprog : funspecs :=
  ltac:(with_library prog [dll_dupleton_spec; malloc_spec]).

Notation "a |~> b" :=
  (data_at Tsh (tarray (Tunion _sslval noattr) 1) [b] a) (at level 1).
Notation "a '|~>' '[' b ';' c ']'" :=
  (data_at Tsh (tarray (Tunion _sslval noattr) 2) [b; c] a) (at level 1).
Notation "'$(int)(' a ')'" := (inl (Vint (Int.repr a))).
Notation "'$(ptr)(' a ')'" := (inr a).
Notation "'int[' n ']'" := (tarray (Tunion _sslval noattr) n).

Lemma body_dll_dupleton : semax_body Vprog Gprog f_dll_dupleton dll_dupleton_spec.
Proof.
start_function.
ssl_open_context.
(*  NilNotLval(r); *)
assert_PROP (isptr r). { entailer!. }
(* Read(Var(a) -> Var(a2),   let a2 = *r); *)
try rename a into a2.
assert_PROP (is_pointer_or_null a2). { entailer!. }
(* evar (_alpha_513z: dll_card).  *)
(* StarPartial(true, not (r == z) && not (z == r)); *)
(* evar (_alpha_513wz: dll_card).  *)
(* StarPartial(true, not (r == wz) && not (wz == r) && not (wz == z) && not (z == wz)); *)
(* SubstR(
   s1z -> {vwz} ++ s1wz
  ); *)
(* SubstR(s1wz -> {}); *)
(* SubstR(wwz -> nullval); *)
(* Malloc(z -> z2,   let z2 = malloc(3)); *)
forward_call (tarray (Tunion _sslval noattr) 3).
Intros z2.
(* StarPartial(not (r == z2) && not (z2 == r), true); *)
(* NilNotLval(z2); *)
assert_PROP (isptr z2). { entailer!. }
(* CheckPost; *)
(* FrameUnfold([z2, 3], [z2, 3]); *)
(* Malloc(wz -> wz2,   let wz2 = malloc(3));  *)
forward_call (tarray (Tunion _sslval noattr) 3).
Intros wz2.
(* StarPartial(not (r == wz2) && not (wz2 == r) && not (wz2 == z2) && not (z2 == wz2), true); *)
(* NilNotLval(wz2); *)
assert_PROP (isptr wz2). { entailer!. }
(* CheckPost; *)
(* FrameUnfold([wz2, 3], [wz2, 3]); *)
(* PickCard(_alpha_515 -> _alpha_513z + 1); *)
(* CheckPost; *)
(* PickCard(_alpha_513z -> _alpha_513wz + 1); *)
(* CheckPost; *)
(* Write(  *r = z2); *)
forward.
(* Write(  *(z2 + 1) = wz2); *)
forward.
(* Write(  *(z2 + 2) = 0); *)
forward.
(* Write(  *(wz2 + 1) = 0); *)
forward.
(* Write(  *(wz2 + 2) = z2); *)
forward.
(* PureSynthesis(true, vwz -> y, vz -> x); *)
(* CheckPost; *)
(* Write(  *z2 = x); *)
forward.
(* Write(  *wz2 = y); *)
forward.
(* WeakenPre((r /= 0) && (r /= wz2) && (r /= z2) && (wz2 /= 0) && (wz2 /= z2) && (z2 /= 0)); *)
(* EmpRule; (end of "symbolic execution of program") *)
forward; entailer!.
(* Evars in reverse order as close rules in proof: *)
evar (_alpha_513wz : dll_card). 
evar (_alpha_513z : dll_card).
evar (_alpha_515: dll_card).
(* Instantiating existentials of goal *)
Exists (_alpha_515 : dll_card).
Exists [Vint (Int.repr x); Vint (Int.repr y)].
Exists z2.
entailer!.
(* Now to handle close rules *)
(* Close(dll(z, 0, {x, y})<_alpha_515>,
  not (x == 0),
  {_alpha_513z < _alpha_515 && {x, y} =i {vz} ++ s1z ;
   [z, 3] **
   z :-> vz **
   (z + 1) :-> wz **
   (z + 2) :-> 0 **
   dll(wz, z, s1z)<_alpha_513z>[0,1]
  }); *)
instantiate (_alpha_515 := (dll_card_1 _alpha_513z)).
simpl (dll _ _ _ ((_alpha_515 : dll_card))) at 1.
Exists (x).
Exists [Vint (Int.repr y)].
Exists wz2.
instantiate (_alpha_513z := (dll_card_1 _alpha_513wz)).
(* Close(dll(wz, z, s1z)<_alpha_513z>[0,1],
    not (x == 0),
   {
     _alpha_513wz < _alpha_513z && s1z =i {vwz} ++ s1wz ;
     [wz, 3] **
      wz :-> vwz **
     (wz + 1) :-> wwz **
     (wz + 2) :-> z **
     dll(wwz, wz, s1wz)<_alpha_513wz>[0,2]
   }) *)
simpl (dll _ _ _ ((_alpha_513z : dll_card))) at 1.
Exists (y).
Exists ([]: list val).
Exists nullval.
(* Close(
    dll(wwz, wz, s1wz)<_alpha_513wz>[0,2],
    x == 0,
    {s1wz =i {} ; emp},
    {
       v -> v,
       w -> w,
       _alpha_513 -> _alpha_513,
       s1 -> s1
    }
); *)
instantiate (_alpha_513wz := dll_card_0).
simpl (dll _ _ _ ((_alpha_513wz  : dll_card))) at 1.
entailer!.
Qed.
