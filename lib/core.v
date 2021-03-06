Require Import VST.floyd.proofauto.

Definition ssl_is_valid_int (x: val) := exists y, x = Vint (Int.repr y) /\  Int.min_signed <= y <= Int.max_signed.

Ltac ssl_open_context :=
  lazymatch goal with
  | [ H:  ssl_is_valid_int ?x |- _ ] =>
    let x1 := fresh x in
    rename x into x1;
    let H2 := fresh H in
    let H3 := fresh H in
    destruct H as [x [H2 H3]]; rewrite H2 in *; ssl_open_context
  | _ => idtac
  end.

Ltac ssl_open :=
  match goal with
  | [ X : ?x = ?x -> _ |- _ ] =>
    let H := fresh in
    pose proof (X (eq_refl x)) as H; rewrite H in *; clear H; simpl
  | _ => fail
  end.
Ltac ssl_dispatch_card :=
      match goal with
      | [ X : ?x, Y: ?x -> ?y <> ?z |- _]  =>
        let H := fresh in
        pose proof (Y X) as H; generalize H; try case y; try intuition; try eexists; auto
      | _ => fail
      end.

Ltac ssl_card_intro H name :=
  generalize H; clear H;
  match goal with
  | [ |- (_ = _) -> _] =>
    intro H; rewrite H in *; simpl
  | [ |-  (exists _ : _, _) -> _] =>
     intro H; case H; intros name; clear H; intros H
  | _ => idtac
  end.

(* Ltac ssl_card_intro H name := *)
(*   match goal with *)
(*     | [ H : _ = _ |- _] => rewrite H in *; simpl *)
(*     | [ H : exists _ : _, _ |- _] => *)
(*       let g := fresh in *)
(*       case H; intros name; clear H; intros H *)
(*     | _ => fail *)
(*   end. *)

Ltac ssl_card_final C H := let H' := fresh H in try (rewrite H in *; rename H into H'; simpl C).

Tactic Notation "ssl_card" constr(C) ident(H)  := ssl_card_final C H.
Tactic Notation "ssl_card" constr(C) ident(H) simple_intropattern(x0)  := ssl_card_intro H x0; ssl_card_final C H.
Tactic Notation "ssl_card" constr(C) ident(H) simple_intropattern(x0) simple_intropattern(x1)  := ssl_card_intro H x0; ssl_card_intro H x1; ssl_card_final C H.
Tactic Notation "ssl_card" constr(C) ident(H) simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2)  := ssl_card_intro H x0; ssl_card_intro H x1; ssl_card_intro H x2; ssl_card_final C H.
Tactic Notation "ssl_card" constr(C) ident(H) simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)   := ssl_card_intro H x0; ssl_card_intro H x1; ssl_card_intro H x2; ssl_card_intro H x3; ssl_card_final C H.
Tactic Notation "ssl_card" constr(C) ident(H) simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) := ssl_card_intro H x0; ssl_card_intro H x1; ssl_card_intro H x2; ssl_card_intro H x3; ssl_card_intro H x4;  ssl_card_final C H.
Tactic Notation "ssl_card" constr(C) ident(H) simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) := ssl_card_intro H x0; ssl_card_intro H x1; ssl_card_intro H x2; ssl_card_intro H x3; ssl_card_intro H x4; ssl_card_intro H x5;  ssl_card_final C H.
Tactic Notation "ssl_card" constr(C) ident(H) simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6) := ssl_card_intro H x0; ssl_card_intro H x1; ssl_card_intro H x2; ssl_card_intro H x3; ssl_card_intro H x4; ssl_card_intro H x5; ssl_card_intro H x6; ssl_card_final C H.
Tactic Notation "ssl_card" constr(C) ident(H) simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) := ssl_card_intro H x0; ssl_card_intro H x1; ssl_card_intro H x2; ssl_card_intro H x3; ssl_card_intro H x4; ssl_card_intro H x5; ssl_card_intro H x6; ssl_card_intro H x7; ssl_card_final C H.
Tactic Notation "ssl_card" constr(C) ident(H) simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8) := ssl_card_intro H x0; ssl_card_intro H x1; ssl_card_intro H x2; ssl_card_intro H x3; ssl_card_intro H x4; ssl_card_intro H x5; ssl_card_intro H x6; ssl_card_intro H x7; ssl_card_intro H x8; ssl_card_final C H.
Tactic Notation "ssl_card" constr(C) ident(H) simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8) simple_intropattern(x9) := ssl_card_intro H x0; ssl_card_intro H x1; ssl_card_intro H x2; ssl_card_intro H x3; ssl_card_intro H x4; ssl_card_intro H x5; ssl_card_intro H x6; ssl_card_intro H x7; ssl_card_intro H x8; ssl_card_intro H x9; ssl_card_final C H.


From mathcomp Require Import eqtype.

(* Define eqtype instance for Z *)
Lemma eqzP : Equality.axiom Z.eqb.
Proof. exact Z.eqb_spec. Qed.

Canonical Z_eqMixin := EqMixin eqzP.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.


Ltac ssl_rewrite_in_heap lemma term :=
  let H := fresh in
  let H_eqn := fresh in
  remember term as H eqn:H_eqn;
  rewrite lemma in H_eqn;
  rewrite H_eqn at 1; clear H H_eqn.

Ltac ssl_rewrite_last_heap lemma term :=
  idtac "rewrite_last_heap2" lemma term;
  lazymatch term with
  | (?X * ?Y)%logic =>  ssl_rewrite_last_heap lemma Y || ssl_rewrite_in_heap lemma X
  | _ => ssl_rewrite_in_heap lemma term
  end.

Ltac ssl_rewrite_last lemma :=
  match goal with
  | [ |- ?H |-- ?V ] => ssl_rewrite_last_heap lemma V
  | _ => rewrite lemma at 20
  | _ => rewrite lemma at 19
  | _ => rewrite lemma at 18
  | _ => rewrite lemma at 17
  | _ => rewrite lemma at 16
  | _ => rewrite lemma at 15
  | _ => rewrite lemma at 14
  | _ => rewrite lemma at 13
  | _ => rewrite lemma at 12
  | _ => rewrite lemma at 11
  | _ => rewrite lemma at 10
  | _ => rewrite lemma at 9
  | _ => rewrite lemma at 8
  | _ => rewrite lemma at 7
  | _ => rewrite lemma at 6
  | _ => rewrite lemma at 5
  | _ => rewrite lemma at 4
  | _ => rewrite lemma at 3
  | _ => rewrite lemma at 2
  | _ => rewrite lemma at 1
  end.


(*==== poor people's tools========*)

(* poor man's ternary *)
Ltac ssl_forward_write_ternary expr :=
  match goal with
  | [ |- (semax _ _ (Ssequence (Ssequence _ (_ ((_ ?X) _))) _) _) ] =>
    forward_if (temp X expr); auto
  end.

Create HintDb ssl_list_facts.
Hint Rewrite app_nil_r : ssl_list_facts.
Hint Rewrite app_nil_l : ssl_list_facts.
Hint Rewrite app_assoc_reverse : ssl_list_facts.
Hint Rewrite app_assoc : ssl_list_facts.
Hint Rewrite app_eq_nil  : ssl_list_facts.

Ltac ssl_safe_entailer_then rest :=
  lazymatch goal with
  | [ |- ?Y |-- ?X ] =>  entailer!; rest
  | _ => auto; rest
  end.

Ltac ssl_safe_entailer := ssl_safe_entailer_then ltac:(idtac).

Ltac ssl_rewrite_lists := 
  repeat lazymatch goal with
       | [H : context[_ ++ _] |- _] => rewrite H
       | [H : context[_ ++ _] |- _] => rewrite <-H
       | [H : context[[]] |- _] => rewrite H
       | [H : context[[]] |- _] => rewrite <-H
       | _ => fail
  end.

Ltac ssl_try_autorewrite := 
  lazymatch goal with
  | [ |- context[_ ++ _] ] =>
    (* if lists, try list facts *)
    autorewrite with ssl_list_facts; ssl_rewrite_lists; ssl_safe_entailer
  | _ => idtac
  end.

Ltac ssl_entailer := ssl_safe_entailer_then ltac:(ssl_try_autorewrite).

(* poor man's reflection (can use hammer for this????) *)
Ltac ssl_reflect_boolean :=
  repeat match goal with
  [ H : ?Y = ?X |- context[?Y =? ?X]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (Y =? X = true) as Hvar; first apply  Z.eqb_eq; auto; last rewrite Hvar; auto
  | [ H : ?X = ?Y |- context[?Y =? ?X]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (Y =? X = true) as Hvar; first apply  Z.eqb_eq; auto; last rewrite Hvar; auto
  | [ H : ?X <> ?Y |- context[?Y =? ?X]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (Y =? X = false) as Hvar; first apply  Z.eqb_neq; auto; last rewrite Hvar; auto
  | [ H : ?Y <> ?X |- context[?Y =? ?X]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (Y =? X = false) as Hvar; first apply  Z.eqb_neq; auto; last rewrite Hvar; auto

  | [ H : ?X > ?Y |- context[?X >? ?Y]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (X >? Y = true) as Hvar; first apply Zgt_is_gt_bool; last rewrite Hvar; auto
  | [ H : ?Y < ?X |- context[?X >? ?Y]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (X >? Y = true) as Hvar; first (apply Zgt_is_gt_bool; apply Z.lt_gt); last rewrite Hvar; auto
  | [ H : ?X < ?Y |- context[?X <? ?Y]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (X <? Y = true) as Hvar; first apply Z.ltb_lt; last rewrite Hvar; auto
  | [ H : ?Y > ?X |- context[?X <? ?Y]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (X <? Y = true) as Hvar; first  (apply Zge_is_le_bool; apply Z.le_ge; apply Z.lt_le_incl; apply Z.gt_lt); last rewrite Hvar; auto
  | [ H : ?X >= ?Y |- context[?Y <=? ?X]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (Y <=? X = true) as Hvar; first apply Zge_is_le_bool; auto; last rewrite Hvar; auto
  | [ H : ?Y <= ?X |- context[?Y <=? ?X]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (Y <=? X = true) as Hvar; first apply Zge_is_le_bool; auto; last rewrite Hvar; auto
  | [ H : ?Y < ?X |- context[?Y <=? ?X]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (Y <=? X = true) as Hvar; first (apply Zge_is_le_bool; apply Z.le_ge; apply Z.lt_le_incl); auto; last rewrite Hvar; auto
  | [ H : ?X > ?Y |- context[?Y <=? ?X]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (Y <=? X = true) as Hvar; first (apply Zge_is_le_bool; apply Z.le_ge; apply Z.lt_le_incl; apply Z.gt_lt); auto; last rewrite Hvar; auto
  | [ H : ?X < ?Y |- context[?Y <=? ?X]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (Y <=? X = false) as Hvar; first apply Zaux.Zle_bool_false; last rewrite Hvar; auto
  | [ H : ?Y > ?X |- context[?Y <=? ?X]] =>
    let Hvar := fresh "H_ssl_helper" in
    assert (Y <=? X = false) as Hvar; first apply Zaux.Zle_bool_false; last rewrite Hvar; auto
  | _ => fail
  end.
