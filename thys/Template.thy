theory Template
  imports Main
  keywords "template" :: thy_decl_block
       and "template_instance" :: thy_goal
begin

ML \<open>

type data = {Ts : string list, ts: (string * typ) list, thms: (string * thm list) list};

fun map_data fT fthm (data : data) =
  {Ts = #Ts data, ts = map (apsnd fT) (#ts data), thms = map (apsnd (map fthm)) (#thms data)};

fun morph_data phi = map_data (Morphism.typ phi) (Morphism.thm phi);

type template = {input : data, output : data};

fun morph_template phi (t : template) =
  {input = morph_data phi (#input t), output = morph_data phi (#output t)};

val transfer_template = morph_template o Morphism.transfer_morphism;

structure Data = Generic_Data
(
  type T = template Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge t : T = Symtab.merge (K true) t;
);

fun template_of_generic context =
  Option.map (transfer_template (Context.theory_of context)) o Symtab.lookup (Data.get context);

val template_of = template_of_generic o Context.Proof;
val template_of_global = template_of_generic o Context.Theory;

fun template_names_of_generic context = distinct (op =) (Symtab.keys (Data.get context));
val template_names_of = template_names_of_generic o Context.Proof;
val template_names_of_global = template_names_of_generic o Context.Theory;

fun export morph (x, (lthy, lthy_old)) =
  (morph (Proof_Context.export_morphism lthy_old lthy) x, lthy);

fun gen_template prepare_constraint prepare_typ prepare_att prepare_prop
    b raw_tycons raw_consts raw_axioms lthy =
  let

    val naming = Name_Space.new_scope (Proof_Context.naming_of (Local_Theory.target_of lthy))
      |-> Name_Space.qualified_scope;
    val lthy = lthy
      |> Local_Theory.map_contexts (K (Proof_Context.map_naming (K naming)))
      |> Local_Theory.map_background_naming Name_Space.concealed;


    val mk_b = Binding.qualify false (Binding.name_of b);

    fun prepare_type_arg (T, c) =
      let val s = fst (dest_TFree (prepare_typ lthy T)) in (s, prepare_constraint lthy c) end;
    fun typedecl ((args, b), mx) lthy = lthy
      |> Local_Theory.open_target |> snd
      |> Typedecl.typedecl {final = true} (mk_b b, map prepare_type_arg args, mx)
      ||> `Local_Theory.close_target
      |> export Morphism.typ;
    val (Ts, lthy) = fold_map typedecl raw_tycons lthy |>> map (dest_Type #> fst);

    val mk_global = Binding.suffix_name "_foundation";

    fun prepare_global (b, T, _) = ((mk_global (mk_b b), prepare_typ lthy T), NoSyn);
    fun define (b, _, mx) t = Local_Theory.define_internal ((mk_b b, mx), ((Binding.empty, []), t))
      #>> fst;
    val gconsts = map prepare_global raw_consts;
    val (ts, lthy) = lthy
      |> Local_Theory.open_target |> snd
      |> Local_Theory.background_theory_result (fold_map (Sign.declare_const_global) gconsts)
      |-> @{fold_map 2} define raw_consts
      ||> `Local_Theory.close_target
      |> export (fn phi => map (Morphism.term phi))
      |>> map dest_Const;

    val (atts, props) = map_split (fn ((b, att), prop) =>
      ((mk_b b, map (prepare_att lthy) att), prepare_prop lthy prop)) raw_axioms;
    val gprops = @{map 2} (pair o rpair [] o mk_global o fst) atts props;
    fun notes thms =
      Local_Theory.notes (atts ~~ map (single o rpair [] o single) thms);

    val (thms, lthy) = lthy
      |> Local_Theory.open_target |> snd
      |> Local_Theory.background_theory_result (Specification.axiomatization [] [] [] gprops #>> snd)
      |-> notes
      ||> `Local_Theory.close_target
      |> export (map o apsnd o Morphism.fact);

    val input = {Ts = Ts, ts = ts, thms = thms} : data;
    val name = Binding.name_of b;

    fun after_close lthy' =
      let
        fun mk_diff eq get = subtract eq (get lthy) (get lthy');

        (* val _ = @{print warning} "new types:"; *)
        val new_Ts = mk_diff (op =) (Type.logical_types o Proof_Context.tsig_of);
        (* val _ = map @{print warning} new_Ts; *)

        (* val _ = @{print tracing} "new constants:"; *)
        val new_ts = mk_diff (fn ((s1, _), (s2, _)) => s1 = s2)
         (#constants o Consts.dest o Proof_Context.consts_of) |> map (apsnd fst);
        (* val _ = map @{print tracing} new_ts; *)

        (* val _ = @{print} "new theorems:"; *)
        val facts = Proof_Context.facts_of lthy;
        val new_thms =  Facts.fold_static (fn (s, thm) => fn thms =>
          (if Facts.defined facts s then I else cons (s, thm)) thms)
          (Proof_Context.facts_of lthy') [];
        (* val _ = map @{print} new_thms; *)

        (* val _ = @{print warning} "nested templates:"; *)
        (* val new_templates = subtract (op =) [name] (mk_diff (op =) template_names_of); *)
        (* val _ = map @{print warning} new_templates; *)

        val output = {Ts = new_Ts, ts = new_ts, thms = new_thms} : data;
        val template = {input = input, output = output} : template;
      in
        lthy'
        |> Local_Theory.declaration {pervasive = true, syntax = false} (fn phi =>
           Data.map (Symtab.update (name, morph_template phi template)))
        |> Local_Theory.close_target
      end;
  in
    lthy
    |> Local_Theory.init_target
      {background_naming = Local_Theory.background_naming_of lthy,
       after_close = after_close}
      (Local_Theory.operations_of lthy)
    |> snd
  end

fun read_constraint _ NONE = @{sort type}
  | read_constraint ctxt (SOME s) = Syntax.read_sort ctxt s;

val template_cmd = gen_template read_constraint Syntax.read_typ Attrib.check_src Syntax.read_prop

val _ =
  Outer_Syntax.command @{command_keyword template} "abstract over type constructors"
    (Parse.binding --
      (@{keyword =} |--
         Parse.!!!
           (Parse.and_list1 (Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix)) --
         Scan.optional (@{keyword fixes} |-- Parse.!!! (Parse.and_list1 Parse.const_binding)) [] --
         Scan.optional (@{keyword assumes} |--
           Parse.!!! (Parse.and_list1 (Parse_Spec.thm_name ":" -- Parse.prop))) []
      --| Parse.begin)
      >> (fn (name, ((tycons, ts), thms)) =>
           Toplevel.open_target
             (Bundle.context [] [] #> snd #> template_cmd name tycons ts thms)));

fun subst_type_constructors substT =
  let
    fun subT (Type (c, Ts)) =
        (case find_first (fn (T, _) => c = fst (dest_Type T)) substT of
          NONE => Type (c, map subT Ts)
        | SOME (Type (_, Us), U) =>
            let
              val theta = Us ~~ map subT Ts;
            in typ_subst_atomic theta U end
        | SOME _ => error "bad type substitution")
    | subT T = T;
  in subT end;

fun subst_term thy substT subst =
  let
    val subT = subst_type_constructors substT;
    fun sub (t $ u) = sub t $ sub u
      | sub (Abs (x, T, t)) =  Abs (x, subT T, sub t)
      | sub (Free (x, T)) = Free (x, subT T)
      | sub (Var (ix, T)) = Var (ix, subT T)
      | sub (Const (c, T)) =
        (case find_first (fn (d, _) => c = fst (dest_Const d)) subst of
          NONE => Const (c, subT T)
        | SOME (Const (_, U), u) => Envir.subst_term
            (Sign.typ_match thy (U, T) Vartab.empty |> Vartab.map (K (apsnd subT)), Vartab.empty) u
        | SOME _ => error "bad type substitution")
      | sub t = t
  in
    sub
  end;

fun gen_template_instance prepare_constraint prepare_type_const prepare_typ prepare_term
    (ib : binding) name raw_substT raw_subst lthy =
  let
    val template = (case template_of lthy name of
        NONE => error "bad template name"
      | SOME template => template);

    fun prepare_type_arg (T, c) =
      let val s = fst (dest_TFree (prepare_typ lthy T)) in TFree (s, prepare_constraint lthy c) end;
    fun prepare_lhs (args, d) =
      Type (prepare_type_const {proper = true, strict = false} lthy d |> dest_Type |> fst,
        map prepare_type_arg args);

    (*FIXME more checks needed*)

    val substT = map (apfst prepare_lhs o apsnd (prepare_typ lthy)) raw_substT;
    val _ = if forall (fn (C, T) =>
      fold_atyps (fn x => fn b => exists_subtype (fn y => x = y) C andalso b) T true) substT then ()
      else error "extra type variables in a type constructor instance";
 
    val subst = map (@{apply 2} (singleton (Variable.polymorphic lthy) o prepare_term lthy)) raw_subst;
    val _ = if forall (fn (c, t) =>
      fold_types (fold_atyps (fn x => fn b => exists_type (exists_subtype (fn y => x = y)) c andalso b)) t true) subst then ()
      else error "extra type variables in a constant instance";

    val phi = Morphism.typ_morphism "subT" (subst_type_constructors substT)
      $>  Morphism.term_morphism "sub" (subst_term (Proof_Context.theory_of lthy) substT subst);

    val goals = template |> #input |> #thms |> maps snd |> map (Morphism.term phi o Thm.prop_of);

    val (mono_goals, _) = Variable.import_terms true goals lthy;

    fun after_qed _ lthy =
      let
        val thy = Proof_Context.theory_of lthy;
        val Ts_names =  template |> #output |> #Ts;
        fun mk_Tdecl T lthy =
          let
            val (As, names_lthy) = Ctr_Sugar_Util.mk_TFrees' (Sign.arity_sorts thy T @{sort type}) lthy
              |>> map dest_TFree;
          in
            ((Binding.qualified_name T, As, NoSyn), names_lthy)
          end;
        val (Tdecls, _) = fold_map mk_Tdecl Ts_names lthy;
        val Ts = @{map 2} (fn T => fn (_, Ts, _) => Type (T, map TFree Ts)) Ts_names Tdecls;
        val (Us, lthy) = lthy
          |> Local_Theory.open_target |> snd
          |> Local_Theory.map_background_naming (Name_Space.qualified_path false ib)
          |> fold_map (Typedecl.typedecl {final = true}) Tdecls
          ||> Local_Theory.close_target;

        val substT' = (Ts ~~ Us) @ substT;

        val ts_names = template |> #output |> #ts;
        fun mk_decl (t, T) lthy =
          let
            val (U, names_lthy) = Variable.importT_terms [Const (@{const_name undefined}, T)] lthy
              |>> (the_single #> dest_Const #> snd);
          in
            (((Binding.qualified_name t, U), NoSyn), names_lthy)
          end;
        val (temp_decls, _) = fold_map mk_decl ts_names lthy;
        val ts = @{map 2} (fn (t, _) => fn ((_, T), _) => Const (t, T)) ts_names temp_decls;
        val decls = map (apfst (apsnd (subst_type_constructors substT'))) temp_decls;

        val (us, lthy) = lthy
          |> Local_Theory.open_target |> snd
          |> Local_Theory.map_background_naming (Name_Space.qualified_path false ib)
          |> Local_Theory.background_theory_result (fold_map (Sign.declare_const_global) decls)
          ||> Local_Theory.close_target;

        val subst' = map (@{apply 2} (singleton (Variable.polymorphic lthy))) (ts ~~ us) @ subst;

        val (thm_names, propss) = template |> #output |> #thms
          |> map_split (apsnd (map (subst_term (Proof_Context.theory_of lthy) substT' subst' o Thm.prop_of)));

        val (mono_props, _) = Variable.import_terms true (flat propss) lthy;
        val axs = map_index (fn (i, prop) =>
          ((Binding.name ("axiom" ^ string_of_int i), []), prop)) mono_props;

        val fixes = fold Term.add_frees mono_props []
          |> map (apfst Binding.name #> apsnd SOME #> rpair NoSyn #> Scan.triple1);

        val ((_, thms), lthy) = lthy
          |> Local_Theory.open_target |> snd
          |> fold Variable.auto_fixes mono_props
          |> Local_Theory.map_background_naming (Name_Space.qualified_path true ib #> Name_Space.concealed)
          |> Local_Theory.background_theory_result (Specification.axiomatization [] fixes [] axs)
          ||> Local_Theory.close_target;
        val notes =
          map (Binding.qualified_name #>
            Binding.qualify false (Binding.name_of ib) #> rpair []) thm_names ~~
          map (map (rpair [] o single)) (unflat propss thms);
      in
        lthy
        |> Local_Theory.notes notes |> snd
      end
  in
    Proof.theorem NONE after_qed (map (single o rpair []) mono_goals) lthy
  end;

val template_instance_cmd = gen_template_instance read_constraint
  Proof_Context.read_type_name Syntax.read_typ Syntax.read_term;

val _ =
  Outer_Syntax.command @{command_keyword template_instance} "instantiate type constructors"
    (Parse.binding --| @{keyword :} -- Parse.name --
      (@{keyword where} |--
         Parse.!!! (Parse.and_list1 ((Parse.type_args_constrained -- Parse.type_const) --| @{keyword =} -- Parse.typ)) --
       (@{keyword for} |--
         Parse.!!! (Parse.and_list1 (Parse.const --| @{keyword =} -- Parse.term))))
      >> (fn ((iname, name), (substT, subst)) =>
           Toplevel.local_theory_to_proof NONE NONE (template_instance_cmd iname name substT subst)));
\<close>

end
