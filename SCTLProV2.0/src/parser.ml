
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | With
    | While
    | Vertical
    | Var
    | Value
    | Underline
    | UIden of (
# 39 "parser.mly"
       (string)
# 17 "parser.ml"
  )
    | True
    | Transition
    | Top
    | Then
    | TUnt
    | TLst
    | TInt
    | TFloat
    | TBool
    | TAray
    | Spec
    | Semicolon
    | RB3
    | RB2
    | RB1
    | Oro
    | Or
    | Non_Equal
    | Next
    | Negb
    | Neg
    | MultDot
    | Mult
    | Model
    | MinusDot
    | Minus
    | Match
    | Let
    | LT
    | LE
    | LB3
    | LB2
    | LB1
    | LArrow
    | Int of (
# 37 "parser.mly"
       (int)
# 56 "parser.ml"
  )
    | Init
    | In
    | Import
    | If
    | Iden of (
# 39 "parser.mly"
       (string)
# 65 "parser.ml"
  )
    | GT
    | GE
    | Function
    | For
    | Float of (
# 38 "parser.mly"
       (float)
# 74 "parser.ml"
  )
    | False
    | Fairness
    | Equal
    | Else
    | EX
    | EU
    | EOF
    | EG
    | DotDot
    | Dot
    | Done
    | Do
    | Datatype
    | Comma
    | ColonColon
    | Colon
    | Bottom
    | Atomic
    | At
    | Assigno
    | Arrow
    | Ando
    | And
    | AddDot
    | Add
    | AX
    | AR
    | AF
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState407
  | MenhirState396
  | MenhirState395
  | MenhirState394
  | MenhirState392
  | MenhirState388
  | MenhirState383
  | MenhirState380
  | MenhirState379
  | MenhirState376
  | MenhirState375
  | MenhirState374
  | MenhirState373
  | MenhirState370
  | MenhirState369
  | MenhirState366
  | MenhirState365
  | MenhirState362
  | MenhirState361
  | MenhirState360
  | MenhirState359
  | MenhirState356
  | MenhirState354
  | MenhirState353
  | MenhirState352
  | MenhirState351
  | MenhirState350
  | MenhirState346
  | MenhirState340
  | MenhirState335
  | MenhirState331
  | MenhirState325
  | MenhirState318
  | MenhirState315
  | MenhirState313
  | MenhirState312
  | MenhirState310
  | MenhirState304
  | MenhirState302
  | MenhirState298
  | MenhirState296
  | MenhirState294
  | MenhirState288
  | MenhirState286
  | MenhirState281
  | MenhirState280
  | MenhirState279
  | MenhirState272
  | MenhirState270
  | MenhirState268
  | MenhirState261
  | MenhirState260
  | MenhirState259
  | MenhirState257
  | MenhirState247
  | MenhirState240
  | MenhirState237
  | MenhirState235
  | MenhirState234
  | MenhirState233
  | MenhirState230
  | MenhirState229
  | MenhirState226
  | MenhirState224
  | MenhirState222
  | MenhirState221
  | MenhirState214
  | MenhirState210
  | MenhirState205
  | MenhirState203
  | MenhirState202
  | MenhirState200
  | MenhirState187
  | MenhirState180
  | MenhirState176
  | MenhirState171
  | MenhirState166
  | MenhirState164
  | MenhirState160
  | MenhirState158
  | MenhirState151
  | MenhirState148
  | MenhirState146
  | MenhirState143
  | MenhirState141
  | MenhirState139
  | MenhirState137
  | MenhirState135
  | MenhirState133
  | MenhirState131
  | MenhirState129
  | MenhirState127
  | MenhirState125
  | MenhirState123
  | MenhirState120
  | MenhirState118
  | MenhirState116
  | MenhirState114
  | MenhirState111
  | MenhirState109
  | MenhirState107
  | MenhirState105
  | MenhirState102
  | MenhirState98
  | MenhirState93
  | MenhirState89
  | MenhirState87
  | MenhirState85
  | MenhirState83
  | MenhirState82
  | MenhirState81
  | MenhirState80
  | MenhirState78
  | MenhirState77
  | MenhirState76
  | MenhirState75
  | MenhirState71
  | MenhirState70
  | MenhirState65
  | MenhirState63
  | MenhirState62
  | MenhirState59
  | MenhirState57
  | MenhirState52
  | MenhirState51
  | MenhirState50
  | MenhirState49
  | MenhirState47
  | MenhirState46
  | MenhirState45
  | MenhirState44
  | MenhirState43
  | MenhirState41
  | MenhirState40
  | MenhirState39
  | MenhirState36
  | MenhirState35
  | MenhirState34
  | MenhirState30
  | MenhirState28
  | MenhirState24
  | MenhirState23
  | MenhirState21
  | MenhirState17
  | MenhirState16
  | MenhirState15
  | MenhirState14
  | MenhirState13
  | MenhirState12
  | MenhirState10
  | MenhirState9
  | MenhirState5
  | MenhirState3
  | MenhirState2
  | MenhirState0

# 1 "parser.mly"
  
    open Ast

    let imported = ref []
    let symbol_tbl:(Ast.psymbol_tbl) = Hashtbl.create 1
    let kripke_model = ref None
    let type_var = ref 0
    let new_type_var () = 
        incr type_var;
        !type_var

    let erase_type_args t args = 
        match args with 
        | [] -> t
        | _ -> 
            let tmp_t = ref t in
            let rec erase_type_args_i pt i = 
                match pt with
                | PTUdt (str, pts) -> 
                    let a = List.nth args i in
                    if a=str then
                        PTVar (-i-1)
                    else 
                        PTUdt (str, List.map (fun pt -> erase_type_args_i pt i) pts) 
                | PTAray pt1 -> PTAray (erase_type_args_i pt1 i) 
                | PTLst pt1 -> PTLst (erase_type_args_i pt1 i)
                | PTTuple pts -> PTTuple (List.map (fun pt -> erase_type_args_i pt i) pts)
                | PTRecord str_pts -> PTRecord (List.map (fun (str, pt) -> (str, erase_type_args_i pt i)) str_pts)
                | _ -> pt
            in
            for i = 0 to (List.length args) do
                tmp_t := erase_type_args_i !tmp_t i
            done;
            !tmp_t
        

# 313 "parser.ml"

let rec _menhir_goto_list_svar_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.pstate list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState318 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Ast.pstate))), _, (xs : (Ast.pstate list))) = _menhir_stack in
        let _v : (Ast.pstate list) = 
# 187 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 326 "parser.ml"
         in
        _menhir_goto_list_svar_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState315 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _endpos_id_, _menhir_s, (id : (
# 39 "parser.mly"
       (string)
# 343 "parser.ml"
            )), _startpos_id_), _startpos__2_), _, (el : (Ast.pstate list))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _startpos = _startpos_id_ in
            let _endpos = _endpos__4_ in
            let _v : (Ast.pformula_loc) = 
# 200 "parser.mly"
                                        (mk_pformula_loc (PAtomic (id,  el)) _startpos_id_ _endpos__4_)
# 352 "parser.ml"
             in
            _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_svar : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.pstate) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState318 | MenhirState315 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            _menhir_run317 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState318 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | UIden _v ->
            _menhir_run316 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState318 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RB1 ->
            _menhir_reduce91 _menhir_env (Obj.magic _menhir_stack) MenhirState318
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState318)
    | MenhirState356 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__8_ = _endpos in
            let ((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_id_, (id : (
# 39 "parser.mly"
       (string)
# 397 "parser.ml"
            )), _startpos_id_), _endpos_f_, _, (f : (Ast.pformula_loc)), _startpos_f_), _), _, (e : (Ast.pstate))) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__8_ in
            let _v : (Ast.pformula_loc) = 
# 206 "parser.mly"
                                                            (mk_pformula_loc (PAF (id, f, e)) _startpos__1_ _endpos__8_)
# 409 "parser.ml"
             in
            _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState362 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__12_ = _endpos in
            let (((((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_id1_, (id1 : (
# 39 "parser.mly"
       (string)
# 432 "parser.ml"
            )), _startpos_id1_), _endpos_id2_, (id2 : (
# 39 "parser.mly"
       (string)
# 436 "parser.ml"
            )), _startpos_id2_), _endpos_f1_, _, (f1 : (Ast.pformula_loc)), _startpos_f1_), _), _endpos_f2_, _, (f2 : (Ast.pformula_loc)), _startpos_f2_), _), _, (e : (Ast.pstate))) = _menhir_stack in
            let _12 = () in
            let _10 = () in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__12_ in
            let _v : (Ast.pformula_loc) = 
# 208 "parser.mly"
                                                                                                  (mk_pformula_loc (PAR (id1, id2, f1, f2, e)) _startpos__1_ _endpos__12_)
# 450 "parser.ml"
             in
            _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState366 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__8_ = _endpos in
            let ((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_id_, (id : (
# 39 "parser.mly"
       (string)
# 473 "parser.ml"
            )), _startpos_id_), _endpos_f_, _, (f : (Ast.pformula_loc)), _startpos_f_), _), _, (e : (Ast.pstate))) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__8_ in
            let _v : (Ast.pformula_loc) = 
# 204 "parser.mly"
                                                            (mk_pformula_loc (PAX (id, f, e)) _startpos__1_ _endpos__8_)
# 485 "parser.ml"
             in
            _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState370 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__8_ = _endpos in
            let ((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_id_, (id : (
# 39 "parser.mly"
       (string)
# 508 "parser.ml"
            )), _startpos_id_), _endpos_f_, _, (f : (Ast.pformula_loc)), _startpos_f_), _), _, (e : (Ast.pstate))) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__8_ in
            let _v : (Ast.pformula_loc) = 
# 207 "parser.mly"
                                                            (mk_pformula_loc (PEG (id, f, e)) _startpos__1_ _endpos__8_)
# 520 "parser.ml"
             in
            _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState376 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__12_ = _endpos in
            let (((((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_id1_, (id1 : (
# 39 "parser.mly"
       (string)
# 543 "parser.ml"
            )), _startpos_id1_), _endpos_id2_, (id2 : (
# 39 "parser.mly"
       (string)
# 547 "parser.ml"
            )), _startpos_id2_), _endpos_f1_, _, (f1 : (Ast.pformula_loc)), _startpos_f1_), _), _endpos_f2_, _, (f2 : (Ast.pformula_loc)), _startpos_f2_), _), _, (e : (Ast.pstate))) = _menhir_stack in
            let _12 = () in
            let _10 = () in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__12_ in
            let _v : (Ast.pformula_loc) = 
# 209 "parser.mly"
                                                                                                  (mk_pformula_loc (PEU (id1, id2, f1, f2, e)) _startpos__1_ _endpos__12_)
# 561 "parser.ml"
             in
            _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState380 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__8_ = _endpos in
            let ((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_id_, (id : (
# 39 "parser.mly"
       (string)
# 584 "parser.ml"
            )), _startpos_id_), _endpos_f_, _, (f : (Ast.pformula_loc)), _startpos_f_), _), _, (e : (Ast.pstate))) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__8_ in
            let _v : (Ast.pformula_loc) = 
# 205 "parser.mly"
                                                            (mk_pformula_loc (PEX (id, f, e)) _startpos__1_ _endpos__8_)
# 596 "parser.ml"
             in
            _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_spec_list : _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * Ast.pformula_loc) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState396 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 618 "parser.ml"
        )), _startpos__1_), _endpos__3_, _, (_3 : (Ast.pformula_loc)), _startpos__3_), _endpos__4_, _), _, (_5 : ((string * Ast.pformula_loc) list))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _v : ((string * Ast.pformula_loc) list) = 
# 150 "parser.mly"
                                                ((_1, _3)::_5)
# 625 "parser.ml"
         in
        _menhir_goto_spec_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState392 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB3 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let ((_menhir_stack, _startpos__2_), _, (_3 : ((string * Ast.pformula_loc) list))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : ((string * Ast.pformula_loc) list) = 
# 146 "parser.mly"
                                  (_3)
# 646 "parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RB3 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__12_ = _endpos in
                let ((((((((((_menhir_stack, _endpos__2_, (_2 : (
# 39 "parser.mly"
       (string)
# 662 "parser.ml"
                )), _startpos__2_), _startpos__3_), _endpos__4_), _startpos__5_), (ovd : (Ast.ptyp option))), (oinit : (Ast.pexpr_loc option))), (trans : (Ast.ppattern_loc * Ast.ptrans_def))), (atomics : ((string * (string list * Ast.pexpr_loc)) list))), (ofairs : (Ast.pformula_loc list option))), (spec : ((string * Ast.pformula_loc) list))) = _menhir_stack in
                let _12 = () in
                let _5 = () in
                let _4 = () in
                let _3 = () in
                let _1 = () in
                let _v : (unit) = 
# 113 "parser.mly"
                                                                                                                                                                             (
            (*choose_action ovd (fun ()->()) (fun t->Hashtbl.add symbol_tbl ($2^"_State") (UDT, PTyp t));
            choose_action oinit (fun()->()) (fun e->Hashtbl.add symbol_tbl "Init" (Val, PExpr_loc (PTVar (new_type_var ()), e)));*)

            begin
                match ovd with
                | None -> ()
                | Some t -> Hashtbl.add symbol_tbl (_2^"_State") (UDT, PTyp t)
            end;
            begin
                match oinit with
                | None -> ()
                | Some e -> Hashtbl.add symbol_tbl "init" (Val, PExpr_loc (PTVar (new_type_var ()), e))
            end;

            kripke_model := Some {
                transition = trans;
                atomic = (let atomic_tbl = Hashtbl.create 1 in
                            List.iter (fun (str, atom) -> Hashtbl.add atomic_tbl str atom) atomics;
                            atomic_tbl    
                        );
                fairness = (
                        match ofairs with
                        | None -> []
                        | Some fl -> fl 
                    );
                
                (* Options.choose_action ofairs (fun ()->[]) (fun fl->fl); *)
                properties = spec;
            }
        )
# 702 "parser.ml"
                 in
                let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | EOF ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (((_menhir_stack, (_1 : (unit))), _, (_2 : (unit))), (_3 : (unit))) = _menhir_stack in
                    let _4 = () in
                    let _v : (
# 45 "parser.mly"
       ((string list) * (Ast.psymbol_tbl) * ((Ast.pkripke_model) option))
# 717 "parser.ml"
                    ) = 
# 76 "parser.mly"
                                   (!imported, symbol_tbl, !kripke_model)
# 721 "parser.ml"
                     in
                    _menhir_goto_program _menhir_env _menhir_stack _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_formula_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.pformula_loc list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState310 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB3 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let ((_menhir_stack, _startpos__2_), _, (fmls : (Ast.pformula_loc list))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Ast.pformula_loc list) = 
# 152 "parser.mly"
                                                            (fmls)
# 766 "parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (x : (Ast.pformula_loc list)) = _v in
            let _v : (Ast.pformula_loc list option) = 
# 102 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( Some x )
# 774 "parser.ml"
             in
            _menhir_goto_option_fair_decl_ _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState388 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (Ast.pformula_loc)), _startpos_x_), _, (xs : (Ast.pformula_loc list))) = _menhir_stack in
        let _v : (Ast.pformula_loc list) = 
# 197 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 790 "parser.ml"
         in
        _menhir_goto_nonempty_list_formula_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run352 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pformula_loc) * Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AF ->
        _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | AR ->
        _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | AX ->
        _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Bottom ->
        _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EG ->
        _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EU ->
        _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EX ->
        _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Neg ->
        _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Top ->
        _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState352

and _menhir_run354 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pformula_loc) * Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AF ->
        _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | AR ->
        _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | AX ->
        _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Bottom ->
        _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState354 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EG ->
        _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EU ->
        _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EX ->
        _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState354 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Neg ->
        _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Top ->
        _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState354 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState354

and _menhir_run393 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 865 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Assigno ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AF ->
            _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState394 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AR ->
            _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState394 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AX ->
            _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState394 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Bottom ->
            _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState394 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EG ->
            _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState394 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EU ->
            _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState394 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EX ->
            _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState394 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Iden _v ->
            _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState394 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState394 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Neg ->
            _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState394 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Top ->
            _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState394 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState394)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce91 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Ast.pstate list) = 
# 185 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 915 "parser.ml"
     in
    _menhir_goto_list_svar_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run316 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 922 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let (_1 : (
# 39 "parser.mly"
       (string)
# 931 "parser.ml"
    )) = _v in
    let _startpos__1_ = _startpos in
    let _v : (Ast.pstate) = 
# 214 "parser.mly"
            (PSVar _1)
# 937 "parser.ml"
     in
    _menhir_goto_svar _menhir_env _menhir_stack _menhir_s _v

and _menhir_run317 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 944 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let (_1 : (
# 39 "parser.mly"
       (string)
# 953 "parser.ml"
    )) = _v in
    let _startpos__1_ = _startpos in
    let _v : (Ast.pstate) = 
# 213 "parser.mly"
            (PSVar _1)
# 959 "parser.ml"
     in
    _menhir_goto_svar _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_formula : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Ast.pformula_loc) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState350 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | And ->
            _menhir_run354 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState351 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run317 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState356 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run316 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState356 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState356)
        | Or ->
            _menhir_run352 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState351)
    | MenhirState352 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | And ->
            _menhir_run354 _menhir_env (Obj.magic _menhir_stack) MenhirState353
        | AF | AR | AX | Bottom | Comma | EG | EU | EX | Iden _ | LB1 | Neg | Or | RB1 | RB3 | Semicolon | Top ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Ast.pformula_loc)), _startpos__1_), _), _endpos__3_, _, (_3 : (Ast.pformula_loc)), _startpos__3_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : (Ast.pformula_loc) = 
# 203 "parser.mly"
                            (mk_pformula_loc (POr (_1, _3)) _startpos__1_ _endpos__3_)
# 1011 "parser.ml"
             in
            _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState353)
    | MenhirState354 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Ast.pformula_loc)), _startpos__1_), _), _endpos__3_, _, (_3 : (Ast.pformula_loc)), _startpos__3_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__3_ in
        let _v : (Ast.pformula_loc) = 
# 202 "parser.mly"
                            (mk_pformula_loc (PAnd (_1, _3)) _startpos__1_ _endpos__3_)
# 1028 "parser.ml"
         in
        _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState346 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | And ->
            _menhir_run354 _menhir_env (Obj.magic _menhir_stack) MenhirState359
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState359 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AF ->
                _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState360 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | AR ->
                _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState360 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | AX ->
                _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState360 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Bottom ->
                _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState360 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EG ->
                _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState360 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EU ->
                _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState360 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EX ->
                _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState360 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState360 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState360 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Neg ->
                _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState360 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Top ->
                _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState360 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState360)
        | Or ->
            _menhir_run352 _menhir_env (Obj.magic _menhir_stack) MenhirState359
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState359)
    | MenhirState360 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | And ->
            _menhir_run354 _menhir_env (Obj.magic _menhir_stack) MenhirState361
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState361 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run317 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState362 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run316 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState362 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState362)
        | Or ->
            _menhir_run352 _menhir_env (Obj.magic _menhir_stack) MenhirState361
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState361)
    | MenhirState340 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | And ->
            _menhir_run354 _menhir_env (Obj.magic _menhir_stack) MenhirState365
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState365 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run317 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState366 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run316 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState366 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState366)
        | Or ->
            _menhir_run352 _menhir_env (Obj.magic _menhir_stack) MenhirState365
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState365)
    | MenhirState335 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | And ->
            _menhir_run354 _menhir_env (Obj.magic _menhir_stack) MenhirState369
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState369 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run317 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState370 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run316 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState370 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState370)
        | Or ->
            _menhir_run352 _menhir_env (Obj.magic _menhir_stack) MenhirState369
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState369)
    | MenhirState331 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | And ->
            _menhir_run354 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState373 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AF ->
                _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState374 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | AR ->
                _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState374 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | AX ->
                _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState374 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Bottom ->
                _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState374 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EG ->
                _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState374 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EU ->
                _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState374 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EX ->
                _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState374 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState374 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState374 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Neg ->
                _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState374 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Top ->
                _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState374 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState374)
        | Or ->
            _menhir_run352 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState373)
    | MenhirState374 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | And ->
            _menhir_run354 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState375 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run317 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState376 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run316 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState376 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState376)
        | Or ->
            _menhir_run352 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState375)
    | MenhirState325 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | And ->
            _menhir_run354 _menhir_env (Obj.magic _menhir_stack) MenhirState379
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState379 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run317 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState380 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run316 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState380 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState380)
        | Or ->
            _menhir_run352 _menhir_env (Obj.magic _menhir_stack) MenhirState379
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState379)
    | MenhirState313 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | And ->
            _menhir_run354 _menhir_env (Obj.magic _menhir_stack) MenhirState383
        | Or ->
            _menhir_run352 _menhir_env (Obj.magic _menhir_stack) MenhirState383
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState383 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Ast.pformula_loc)), _startpos__2_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : (Ast.pformula_loc) = 
# 210 "parser.mly"
                      (_2)
# 1287 "parser.ml"
             in
            _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState383)
    | MenhirState312 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Ast.pformula_loc)), _startpos__2_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__2_ in
        let _v : (Ast.pformula_loc) = 
# 201 "parser.mly"
                    (mk_pformula_loc (PNeg _2) _startpos__1_ _endpos__2_)
# 1304 "parser.ml"
         in
        _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState388 | MenhirState310 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AF ->
            _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState388 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AR ->
            _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState388 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AX ->
            _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState388 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | And ->
            _menhir_run354 _menhir_env (Obj.magic _menhir_stack) MenhirState388
        | Bottom ->
            _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState388 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EG ->
            _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState388 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EU ->
            _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState388 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EX ->
            _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState388 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Iden _v ->
            _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState388 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState388 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Neg ->
            _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState388 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Or ->
            _menhir_run352 _menhir_env (Obj.magic _menhir_stack) MenhirState388
        | Top ->
            _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState388 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RB3 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_x_, _menhir_s, (x : (Ast.pformula_loc)), _startpos_x_) = _menhir_stack in
            let _v : (Ast.pformula_loc list) = 
# 195 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( [ x ] )
# 1344 "parser.ml"
             in
            _menhir_goto_nonempty_list_formula_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState388)
    | MenhirState394 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | And ->
            _menhir_run354 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Or ->
            _menhir_run352 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Semicolon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState395 in
            let _menhir_stack = (_menhir_stack, _endpos, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run393 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState396 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RB3 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 1375 "parser.ml"
                )), _startpos__1_), _endpos__3_, _, (_3 : (Ast.pformula_loc)), _startpos__3_), _endpos__4_, _) = _menhir_stack in
                let _4 = () in
                let _2 = () in
                let _v : ((string * Ast.pformula_loc) list) = 
# 149 "parser.mly"
                                            ([(_1, _3)])
# 1382 "parser.ml"
                 in
                _menhir_goto_spec_list _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState396)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState395)
    | _ ->
        _menhir_fail ()

and _menhir_goto_atomic_paras : _menhir_env -> 'ttv_tail -> _menhir_state -> (string list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState298 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 1406 "parser.ml"
        )), _startpos__1_), _, (_3 : (string list))) = _menhir_stack in
        let _2 = () in
        let _v : (string list) = 
# 162 "parser.mly"
                                (_1::_3)
# 1412 "parser.ml"
         in
        _menhir_goto_atomic_paras _menhir_env _menhir_stack _menhir_s _v
    | MenhirState296 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Assigno ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | False ->
                    _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Float _v ->
                    _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState302 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | For ->
                    _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Iden _v ->
                    _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState302 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | If ->
                    _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Int _v ->
                    _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState302 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB1 ->
                    _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB2 ->
                    _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB3 ->
                    _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Let ->
                    _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Match ->
                    _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Minus ->
                    _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | MinusDot ->
                    _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Negb ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | True ->
                    _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | UIden _v ->
                    _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState302 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | While ->
                    _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState302)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_pattern_expr_list : _menhir_env -> 'ttv_tail -> Lexing.position -> ((Ast.ppattern_loc * Ast.pexpr_loc) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _v ->
    let _menhir_stack = (_menhir_stack, _endpos, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Vertical ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Float _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState200 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Iden _v ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState200 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Int _v ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState200 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB2 ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | UIden _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState200 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Underline ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState200 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState200)
    | Add | AddDot | Ando | At | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LArrow | LB2 | LE | LT | Minus | MinusDot | Model | Mult | MultDot | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | With ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e1_, _, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_pel_, (pel : ((Ast.ppattern_loc * Ast.pexpr_loc) list))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_pel_ in
        let _v : (Ast.pexpr_loc) = 
# 353 "parser.mly"
                                                          (mk_pexpr_loc (PMatch (e1, pel)) (PTVar (new_type_var ())) _startpos__1_ _endpos_pel_)
# 1525 "parser.ml"
         in
        _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_separated_nonempty_list_Comma_expr_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.pexpr_loc list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState176 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (Ast.pexpr_loc))), _, (el : (Ast.pexpr_loc list))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__5_ in
            let _v : (Ast.pexpr_loc) = 
# 290 "parser.mly"
                                                                       (
            let elt = List.map (fun (e:pexpr_loc) -> e.ptyp) (e::el) in
            mk_pexpr_loc (PTuple (e::el)) ((PTTuple elt)) _startpos__1_ _endpos__5_
        )
# 1562 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState180 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (Ast.pexpr_loc))), _, (xs : (Ast.pexpr_loc list))) = _menhir_stack in
        let _2 = () in
        let _v : (Ast.pexpr_loc list) = 
# 217 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 1579 "parser.ml"
         in
        _menhir_goto_separated_nonempty_list_Comma_expr_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_else_expr_ : _menhir_env -> 'ttv_tail -> Lexing.position -> (Ast.pexpr_loc option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_oe_ = _endpos in
    let (oe : (Ast.pexpr_loc option)) = _v in
    let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e1_, _, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc))) = _menhir_stack in
    let _3 = () in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos_oe_ in
    let _v : (Ast.pexpr_loc) = 
# 337 "parser.mly"
                                                                  (
            match oe with
            | None -> begin
                    mk_pexpr_loc (PIF (e1, e2, None)) PTUnt _startpos__1_ _endpos_oe_
                end
            | Some e3 -> begin
                    mk_pexpr_loc (PIF (e1, e2, oe)) e2.ptyp _startpos__1_ _endpos_oe_
                end
        )
# 1607 "parser.ml"
     in
    _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_option_fair_decl_ : _menhir_env -> 'ttv_tail -> (Ast.pformula_loc list option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Spec ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LB3 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run393 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState392 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState392)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run311 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Ast.pformula_loc) = 
# 198 "parser.mly"
             (mk_pformula_loc PTop _startpos__1_ _endpos__1_)
# 1659 "parser.ml"
     in
    _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run312 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AF ->
        _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState312 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | AR ->
        _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState312 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | AX ->
        _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState312 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Bottom ->
        _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState312 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EG ->
        _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState312 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EU ->
        _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState312 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EX ->
        _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState312 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState312 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState312 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Neg ->
        _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState312 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Top ->
        _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState312 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState312

and _menhir_run313 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AF ->
        _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | AR ->
        _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | AX ->
        _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Bottom ->
        _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState313 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EG ->
        _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EU ->
        _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EX ->
        _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState313 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Neg ->
        _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Top ->
        _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState313 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState313

and _menhir_run314 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 1732 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LB1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            _menhir_run317 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState315 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | UIden _v ->
            _menhir_run316 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState315 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RB1 ->
            _menhir_reduce91 _menhir_env (Obj.magic _menhir_stack) MenhirState315
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState315)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run322 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LB1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Comma ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | AF ->
                    _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState325 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | AR ->
                    _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState325 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | AX ->
                    _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState325 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Bottom ->
                    _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState325 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EG ->
                    _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState325 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EU ->
                    _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState325 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EX ->
                    _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState325 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Iden _v ->
                    _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState325 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB1 ->
                    _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState325 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Neg ->
                    _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState325 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Top ->
                    _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState325 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState325)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _menhir_s, _), _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run326 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LB1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Comma ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | Iden _v ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | Comma ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | AF ->
                            _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | AR ->
                            _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | AX ->
                            _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | Bottom ->
                            _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState331 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | EG ->
                            _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | EU ->
                            _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | EX ->
                            _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | Iden _v ->
                            _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState331 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | LB1 ->
                            _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | Neg ->
                            _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | Top ->
                            _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState331 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState331)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let ((((_menhir_stack, _menhir_s, _), _), _, _, _), _, _, _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (((_menhir_stack, _menhir_s, _), _), _, _, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _menhir_s, _), _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run332 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LB1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Comma ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | AF ->
                    _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState335 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | AR ->
                    _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState335 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | AX ->
                    _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState335 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Bottom ->
                    _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState335 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EG ->
                    _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState335 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EU ->
                    _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState335 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EX ->
                    _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState335 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Iden _v ->
                    _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState335 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB1 ->
                    _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState335 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Neg ->
                    _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState335 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Top ->
                    _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState335 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState335)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _menhir_s, _), _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run336 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Ast.pformula_loc) = 
# 199 "parser.mly"
             (mk_pformula_loc PBottom _startpos__1_ _endpos__1_)
# 2013 "parser.ml"
     in
    _menhir_goto_formula _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run337 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LB1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Comma ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | AF ->
                    _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState340 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | AR ->
                    _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState340 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | AX ->
                    _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState340 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Bottom ->
                    _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState340 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EG ->
                    _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState340 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EU ->
                    _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState340 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EX ->
                    _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState340 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Iden _v ->
                    _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState340 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB1 ->
                    _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState340 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Neg ->
                    _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState340 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Top ->
                    _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState340 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState340)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _menhir_s, _), _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run341 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LB1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Comma ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | Iden _v ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | Comma ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | AF ->
                            _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | AR ->
                            _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | AX ->
                            _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | Bottom ->
                            _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | EG ->
                            _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | EU ->
                            _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | EX ->
                            _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | Iden _v ->
                            _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState346 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | LB1 ->
                            _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | Neg ->
                            _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | Top ->
                            _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState346 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState346)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let ((((_menhir_stack, _menhir_s, _), _), _, _, _), _, _, _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (((_menhir_stack, _menhir_s, _), _), _, _, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _menhir_s, _), _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run347 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LB1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Comma ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | AF ->
                    _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState350 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | AR ->
                    _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState350 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | AX ->
                    _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState350 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Bottom ->
                    _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState350 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EG ->
                    _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState350 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EU ->
                    _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState350 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | EX ->
                    _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState350 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Iden _v ->
                    _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState350 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB1 ->
                    _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState350 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Neg ->
                    _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState350 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Top ->
                    _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState350 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState350)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _menhir_s, _), _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run297 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 2258 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Comma ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            _menhir_run297 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState298 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState298)
    | RB1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 2281 "parser.ml"
        )), _startpos__1_) = _menhir_stack in
        let _v : (string list) = 
# 161 "parser.mly"
                    ([_1])
# 2286 "parser.ml"
         in
        _menhir_goto_atomic_paras _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_transition_def : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ptrans_def) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RB3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__7_ = _endpos in
        let ((((_menhir_stack, _startpos__2_), _endpos_p_, _, (p : (Ast.ppattern_loc)), _startpos_p_), _), _, (_6 : (Ast.ptrans_def))) = _menhir_stack in
        let _7 = () in
        let _5 = () in
        let _3 = () in
        let _2 = () in
        let _1 = () in
        let _v : (Ast.ppattern_loc * Ast.ptrans_def) = 
# 165 "parser.mly"
                                                                     ((p, _6))
# 2318 "parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Atomic ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LB3 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | Iden _v ->
                    _menhir_run295 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState294 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState294)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce22 : _menhir_env -> (('ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * (Ast.pexpr_loc list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((_menhir_stack, _endpos_e_, _menhir_s, (e : (Ast.pexpr_loc)), _startpos_e_), _endpos__2_), _endpos_el_, _, (el : (Ast.pexpr_loc list))) = _menhir_stack in
    let _2 = () in
    let _endpos = _endpos_el_ in
    let _v : (Ast.pexpr_loc) = 
# 254 "parser.mly"
                                                                                        (
            mk_pexpr_loc (PSeq (e::el)) (PTVar (new_type_var())) _startpos_e_ _endpos_el_
        )
# 2370 "parser.ml"
     in
    _menhir_goto_expr _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_goto_expr : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Ast.pexpr_loc) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState146 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Done ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__11_ = _endpos in
            let (((((((_menhir_stack, _menhir_s, _startpos__1_), _endpos_str_, (str : (
# 39 "parser.mly"
       (string)
# 2392 "parser.ml"
            )), _startpos_str_), _startpos__4_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_), _endpos_e3_, _, (e3 : (Ast.pexpr_loc)), _startpos_e3_), _endpos__8_), _endpos_e4_, _, (e4 : (Ast.pexpr_loc))) = _menhir_stack in
            let _11 = () in
            let _9 = () in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__11_ in
            let _v : (Ast.pexpr_loc) = 
# 349 "parser.mly"
                                                                                           (
            mk_pexpr_loc (PFor (str, e2, e3, e4)) (PTUnt) _startpos__1_ _endpos__11_
        )
# 2408 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState164 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Else ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState166 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState166)
        | Add | AddDot | Ando | At | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Equal | Function | GE | GT | LArrow | LB2 | LE | LT | Minus | MinusDot | Model | Mult | MultDot | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical | With ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_, _endpos) = Obj.magic _menhir_stack in
            let _v : (Ast.pexpr_loc option) = 
# 100 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( None )
# 2471 "parser.ml"
             in
            _menhir_goto_option_else_expr_ _menhir_env _menhir_stack _endpos _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__2_, _, (_2 : (Ast.pexpr_loc))) = _menhir_stack in
        let _1 = () in
        let _endpos = _endpos__2_ in
        let _v : (Ast.pexpr_loc) = 
# 394 "parser.mly"
                        (_2)
# 2489 "parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos_x_ = _endpos in
        let (x : (Ast.pexpr_loc)) = _v in
        let _endpos = _endpos_x_ in
        let _v : (Ast.pexpr_loc option) = 
# 102 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( Some x )
# 2499 "parser.ml"
         in
        _menhir_goto_option_else_expr_ _menhir_env _menhir_stack _endpos _v
    | MenhirState83 | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState176 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState176 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState176 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState176 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState176)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState180 | MenhirState176 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState180 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState180)
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_x_, _menhir_s, (x : (Ast.pexpr_loc))) = _menhir_stack in
            let _v : (Ast.pexpr_loc list) = 
# 215 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( [ x ] )
# 2610 "parser.ml"
             in
            _menhir_goto_separated_nonempty_list_Comma_expr_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState203 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Ast.ppattern_loc)), _startpos__1_), _), _endpos__3_, _, (_3 : (Ast.pexpr_loc))) = _menhir_stack in
        let _2 = () in
        let _endpos = _endpos__3_ in
        let _v : (Ast.ppattern_loc * Ast.pexpr_loc) = 
# 400 "parser.mly"
                                    ((_1, _3))
# 2628 "parser.ml"
         in
        (match _menhir_s with
        | MenhirState200 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let (_3 : (Ast.ppattern_loc * Ast.pexpr_loc)) = _v in
            let (_menhir_stack, _endpos__1_, (_1 : ((Ast.ppattern_loc * Ast.pexpr_loc) list))) = _menhir_stack in
            let _2 = () in
            let _endpos = _endpos__3_ in
            let _v : ((Ast.ppattern_loc * Ast.pexpr_loc) list) = 
# 398 "parser.mly"
                                                (_1 @ [_3])
# 2642 "parser.ml"
             in
            _menhir_goto_pattern_expr_list _menhir_env _menhir_stack _endpos _v
        | MenhirState205 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos_pe_ = _endpos in
            let (pe : (Ast.ppattern_loc * Ast.pexpr_loc)) = _v in
            let (_menhir_stack, (_1 : (unit option))) = _menhir_stack in
            let _endpos = _endpos_pe_ in
            let _v : ((Ast.ppattern_loc * Ast.pexpr_loc) list) = 
# 397 "parser.mly"
                                                      ([pe])
# 2655 "parser.ml"
             in
            _menhir_goto_pattern_expr_list _menhir_env _menhir_stack _endpos _v
        | _ ->
            _menhir_fail ())
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Done ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e1_, _, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__5_ in
            let _v : (Ast.pexpr_loc) = 
# 346 "parser.mly"
                                               (
            mk_pexpr_loc (PWhile (e1, e2)) (PTUnt) _startpos__1_ _endpos__5_
        )
# 2682 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState226 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), _endpos_id_, (id : (
# 39 "parser.mly"
       (string)
# 2697 "parser.ml"
        )), _startpos_id_), _, (ags : (Ast.ppattern_loc list))), _, (otf : (Ast.ptyp option))), _endpos_e_, _, (e : (Ast.pexpr_loc))) = _menhir_stack in
        let _5 = () in
        let _1 = () in
        let _v : (unit) = 
# 99 "parser.mly"
                                                                               (
        (* print_endline ("declared function "^id); *)
        match otf with
        | None -> Hashtbl.add symbol_tbl id (Function, PFunction(PTVar (new_type_var ()), ags, e))
        | Some pt -> Hashtbl.add symbol_tbl id (Function, PFunction(pt, ags, e)))
# 2708 "parser.ml"
         in
        _menhir_goto_declare _menhir_env _menhir_stack _menhir_s _v
    | MenhirState281 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Ast.pexpr_loc))) = _menhir_stack in
        let _v : (Ast.ptrans_def) = 
# 184 "parser.mly"
            (PNo_case _1)
# 2718 "parser.ml"
         in
        _menhir_goto_transition_def _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run101 : _menhir_env -> 'ttv_tail * _menhir_state * ((string * Ast.pexpr_loc) list) -> Lexing.position -> (
# 39 "parser.mly"
       (string)
# 2727 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Equal ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | False ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Float _v ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState102 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | For ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Iden _v ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState102 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | If ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Int _v ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState102 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB2 ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB3 ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Let ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Match ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Negb ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | True ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | UIden _v ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState102 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | While ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState102)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_expr_path : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (string list) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    match _menhir_s with
    | MenhirState302 | MenhirState281 | MenhirState286 | MenhirState288 | MenhirState270 | MenhirState226 | MenhirState39 | MenhirState40 | MenhirState214 | MenhirState41 | MenhirState43 | MenhirState44 | MenhirState45 | MenhirState46 | MenhirState203 | MenhirState77 | MenhirState80 | MenhirState81 | MenhirState82 | MenhirState187 | MenhirState83 | MenhirState180 | MenhirState176 | MenhirState85 | MenhirState171 | MenhirState87 | MenhirState166 | MenhirState164 | MenhirState89 | MenhirState158 | MenhirState93 | MenhirState143 | MenhirState146 | MenhirState148 | MenhirState151 | MenhirState102 | MenhirState105 | MenhirState107 | MenhirState109 | MenhirState111 | MenhirState114 | MenhirState116 | MenhirState141 | MenhirState139 | MenhirState137 | MenhirState135 | MenhirState133 | MenhirState125 | MenhirState127 | MenhirState131 | MenhirState129 | MenhirState123 | MenhirState118 | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__1_ = _endpos in
        let (_1 : (string list)) = _v in
        let _startpos__1_ = _startpos in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__1_ in
        let _v : (Ast.pexpr_loc) = 
# 266 "parser.mly"
                       (mk_pexpr_loc (PSymbol _1) (PTVar (new_type_var ())) _startpos__1_ _endpos__1_)
# 2798 "parser.ml"
         in
        _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState160 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__3_ = _endpos in
        let (_3 : (string list)) = _v in
        let _startpos__3_ = _startpos in
        let (_menhir_stack, _endpos_id_, _menhir_s, (id : (
# 39 "parser.mly"
       (string)
# 2810 "parser.ml"
        )), _startpos_id_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos_id_ in
        let _endpos = _endpos__3_ in
        let _v : (string list) = 
# 263 "parser.mly"
                              (id::_3)
# 2818 "parser.ml"
         in
        _menhir_goto_expr_path _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState210 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__3_ = _endpos in
        let (_3 : (string list)) = _v in
        let _startpos__3_ = _startpos in
        let ((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 2830 "parser.ml"
        )), _startpos__1_), _) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__3_ in
        let _v : (Ast.pexpr_loc) = 
# 267 "parser.mly"
                          (mk_pexpr_loc (PSymbol (_1::_3)) (PTVar (new_type_var ())) _startpos__1_ _endpos__3_)
# 2838 "parser.ml"
         in
        _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_atomic_def_list : _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * (string list * Ast.pexpr_loc)) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState304 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 2854 "parser.ml"
        )), _startpos__1_), _startpos__2_), _, (_3 : (string list))), _endpos__4_), _endpos_e_, _, (e : (Ast.pexpr_loc)), _startpos_e_), _endpos__7_), _, (_8 : ((string * (string list * Ast.pexpr_loc)) list))) = _menhir_stack in
        let _7 = () in
        let _5 = () in
        let _4 = () in
        let _2 = () in
        let _v : ((string * (string list * Ast.pexpr_loc)) list) = 
# 158 "parser.mly"
                                                                                     ((_1, (_3, e))::_8)
# 2863 "parser.ml"
         in
        _menhir_goto_atomic_def_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState294 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB3 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let ((_menhir_stack, _startpos__2_), _, (_3 : ((string * (string list * Ast.pexpr_loc)) list))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : ((string * (string list * Ast.pexpr_loc)) list) = 
# 155 "parser.mly"
                                            (_3)
# 2884 "parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Fairness ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LB3 ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_stack = (_menhir_stack, _startpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | AF ->
                        _menhir_run347 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | AR ->
                        _menhir_run341 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | AX ->
                        _menhir_run337 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | Bottom ->
                        _menhir_run336 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | EG ->
                        _menhir_run332 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | EU ->
                        _menhir_run326 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | EX ->
                        _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | Iden _v ->
                        _menhir_run314 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState310 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LB1 ->
                        _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | Neg ->
                        _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | Top ->
                        _menhir_run311 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState310 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState310)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    raise _eRR)
            | Spec ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _v : (Ast.pformula_loc list option) = 
# 100 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( None )
# 2939 "parser.ml"
                 in
                _menhir_goto_option_fair_decl_ _menhir_env _menhir_stack _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run295 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 2959 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LB1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            _menhir_run297 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState296 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState296)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_transition_items : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Ast.pexpr_loc * Ast.pexpr_loc) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState281 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_1 : ((Ast.pexpr_loc * Ast.pexpr_loc) list)) = _v in
        let _v : (Ast.ptrans_def) = 
# 183 "parser.mly"
                                 (PCase _1)
# 2996 "parser.ml"
         in
        _menhir_goto_transition_def _menhir_env _menhir_stack _menhir_s _v
    | MenhirState288 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_5 : ((Ast.pexpr_loc * Ast.pexpr_loc) list)) = _v in
        let (((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_), _endpos__4_) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _v : ((Ast.pexpr_loc * Ast.pexpr_loc) list) = 
# 188 "parser.mly"
                                                                         ((e1, e2)::_5)
# 3009 "parser.ml"
         in
        _menhir_goto_transition_items _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run286 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState286 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState286 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState286 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState286 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState286 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState286

and _menhir_goto_var_expr_list : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> ((string * Ast.pexpr_loc) list) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState272 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 3069 "parser.ml"
        )), _startpos__1_), _endpos__3_, _, (_3 : (Ast.pexpr_loc)), _startpos__3_), _endpos__4_), _endpos__5_, _, (_5 : ((string * Ast.pexpr_loc) list)), _startpos__5_) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__5_ in
        let _v : ((string * Ast.pexpr_loc) list) = 
# 172 "parser.mly"
                                                        ((_1, _3)::_5)
# 3078 "parser.ml"
         in
        _menhir_goto_var_expr_list _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState268 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB3 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let ((_menhir_stack, _startpos__2_), _endpos__3_, _, (_3 : ((string * Ast.pexpr_loc) list)), _startpos__3_) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Ast.pexpr_loc) = 
# 168 "parser.mly"
                                      (mk_pexpr_loc (PRecord (_3)) (PTVar (new_type_var ())) _startpos__3_ _endpos__3_)
# 3099 "parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (x : (Ast.pexpr_loc)) = _v in
            let _v : (Ast.pexpr_loc option) = 
# 102 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( Some x )
# 3107 "parser.ml"
             in
            _menhir_goto_option_init_decl_ _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_declare : _menhir_env -> 'ttv_tail -> _menhir_state -> (unit) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (_1 : (unit))) = _menhir_stack in
            let _2 = () in
            let _v : (
# 46 "parser.mly"
        (unit)
# 3136 "parser.ml"
            ) = 
# 70 "parser.mly"
                   ()
# 3140 "parser.ml"
             in
            _menhir_goto_debug _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState407 | MenhirState247 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Datatype ->
            _menhir_run228 _menhir_env (Obj.magic _menhir_stack) MenhirState407
        | Function ->
            _menhir_run220 _menhir_env (Obj.magic _menhir_stack) MenhirState407
        | Value ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState407
        | EOF | Model ->
            _menhir_reduce18 _menhir_env (Obj.magic _menhir_stack) MenhirState407
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState407)
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_Vertical_ : _menhir_env -> 'ttv_tail -> (unit option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Float _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState205 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState205 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState205 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState205 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Underline ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState205 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState205

and _menhir_run98 : _menhir_env -> ('ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RB3 ->
        _menhir_reduce143 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98

and _menhir_goto_expr_single_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.pexpr_loc list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RB2 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__5_ = _endpos in
                let (((_menhir_stack, _menhir_s, _startpos__1_), _), _, (el : (Ast.pexpr_loc list))) = _menhir_stack in
                let _5 = () in
                let _4 = () in
                let _2 = () in
                let _1 = () in
                let _startpos = _startpos__1_ in
                let _endpos = _endpos__5_ in
                let _v : (Ast.pexpr_loc) = 
# 271 "parser.mly"
                                                        (
            let ea = el in
            if List.length ea = 0 then
                mk_pexpr_loc (PAray ea) (PTAray (PTVar (new_type_var ()))) _startpos__1_ _endpos__5_
            else begin
                let e0 = List.hd ea in
                mk_pexpr_loc (PAray ea) (PTAray e0.ptyp) _startpos__1_ _endpos__5_
            end 
        )
# 3248 "parser.ml"
                 in
                _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState187 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Ast.pexpr_loc)), _startpos__1_), _endpos__2_), _, (_3 : (Ast.pexpr_loc list))) = _menhir_stack in
        let _2 = () in
        let _v : (Ast.pexpr_loc list) = 
# 386 "parser.mly"
                                             (_1::_3)
# 3271 "parser.ml"
         in
        _menhir_goto_expr_single_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB2 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (el : (Ast.pexpr_loc list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : (Ast.pexpr_loc) = 
# 280 "parser.mly"
                                       (
            if List.length el = 0 then
                mk_pexpr_loc (PLst el) (PTLst (PTVar (new_type_var ()))) _startpos__1_ _endpos__3_
            else begin
                let e0 = List.hd el in
                mk_pexpr_loc (PLst el) (PTLst e0.ptyp) _startpos__1_ _endpos__3_
            end
        )
# 3300 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run174 : _menhir_env -> ('ttv_tail * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__3_ = _endpos in
    let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Ast.pexpr_loc)), _startpos__2_) = _menhir_stack in
    let _3 = () in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__3_ in
    let _v : (Ast.pexpr_loc) = 
# 381 "parser.mly"
                           (_2)
# 3325 "parser.ml"
     in
    _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_separated_nonempty_list_Comma_expr_single_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Ast.pexpr_loc list) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _endpos_id_, _menhir_s, (id : (
# 39 "parser.mly"
       (string)
# 3347 "parser.ml"
            )), _startpos_id_), _startpos__2_), _endpos_el_, _, (el : (Ast.pexpr_loc list)), _startpos_el_) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _startpos = _startpos_id_ in
            let _endpos = _endpos__4_ in
            let _v : (Ast.pexpr_loc) = 
# 359 "parser.mly"
                                                                         (
            if List.length el = 1 then
                let eh:pexpr_loc = List.hd el in
                mk_pexpr_loc (POp (id, [eh])) (PTVar (new_type_var ())) _startpos_id_ _endpos_el_
            else 
                mk_pexpr_loc (POp (id, [(mk_pexpr_loc (PTuple el) (PTTuple (List.map (fun (e:pexpr_loc)->e.ptyp) el)) _startpos_el_ _endpos_el_ )])) (PTVar (new_type_var ())) _startpos_id_ _endpos_el_
        )
# 3362 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState158 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (Ast.pexpr_loc)), _startpos_x_), _endpos_xs_, _, (xs : (Ast.pexpr_loc list)), _startpos_xs_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_xs_ in
        let _v : (Ast.pexpr_loc list) = 
# 217 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 3381 "parser.ml"
         in
        _menhir_goto_separated_nonempty_list_Comma_expr_single_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_Semicolon_expr_single_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Ast.pexpr_loc list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState148 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce22 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState151 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos_x_, _menhir_s, (x : (Ast.pexpr_loc)), _startpos_x_), _endpos__2_), _endpos_xs_, _, (xs : (Ast.pexpr_loc list))) = _menhir_stack in
        let _2 = () in
        let _endpos = _endpos_xs_ in
        let _v : (Ast.pexpr_loc list) = 
# 217 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 3403 "parser.ml"
         in
        _menhir_goto_separated_nonempty_list_Semicolon_expr_single_ _menhir_env _menhir_stack _endpos _menhir_s _v
    | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let ((((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (Ast.pexpr_loc)), _startpos_e_), _endpos__3_), _endpos_el_, _, (el : (Ast.pexpr_loc list))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _endpos = _endpos__5_ in
            let _v : (Ast.pexpr_loc) = 
# 257 "parser.mly"
                                                                                               (
            mk_pexpr_loc (PSeq (e::el)) (PTVar (new_type_var())) _startpos_e_ _endpos_el_
        )
# 3427 "parser.ml"
             in
            _menhir_goto_expr _menhir_env _menhir_stack _endpos _menhir_s _v
        | Comma ->
            _menhir_reduce22 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce21 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Ast.pexpr_loc)), _startpos__1_) = _menhir_stack in
    let _endpos = _endpos__1_ in
    let _v : (Ast.pexpr_loc) = 
# 253 "parser.mly"
                  (_1)
# 3448 "parser.ml"
     in
    _menhir_goto_expr _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_run148 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_stack = (_menhir_stack, _endpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState148 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState148

and _menhir_goto_str_expr_list : _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * Ast.pexpr_loc) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RB3 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let (((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _startpos__3_), _, (str_el : ((string * Ast.pexpr_loc) list))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos__5_ in
            let _v : (Ast.pexpr_loc) = 
# 354 "parser.mly"
                                                              (mk_pexpr_loc (PWith (e1, str_el)) e1.ptyp _startpos_e1_ _endpos__5_)
# 3523 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RB3 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (str_el : ((string * Ast.pexpr_loc) list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : (Ast.pexpr_loc) = 
# 294 "parser.mly"
                                     (
            let str_elt = List.map (fun (str, (pel:pexpr_loc)) -> (str, pel.ptyp)) str_el in
            mk_pexpr_loc (PRecord str_el) (PTRecord str_elt) _startpos__1_ _endpos__3_
        )
# 3556 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run97 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LB3 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run105 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState105

and _menhir_run107 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState107 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState107 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState107 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState107 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState107

and _menhir_run109 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState109

and _menhir_run114 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState114 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState114 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState114 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState114 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState114

and _menhir_run118 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState118 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState118 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState118 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState118 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState118

and _menhir_run123 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState123 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState123 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState123 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState123 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState123

and _menhir_run125 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState125 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState125 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState125 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState125 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState125

and _menhir_run133 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState133 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState133

and _menhir_run111 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState111 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState111

and _menhir_run116 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState116 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState116 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState116 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState116 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116

and _menhir_run135 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState135 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState135 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState135 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState135 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState135

and _menhir_run137 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState137 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState137 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState137 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState137 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState137

and _menhir_run127 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState127

and _menhir_run139 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState139 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState139 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState139 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState139 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState139

and _menhir_run120 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState120 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState120

and _menhir_run141 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState141 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState141 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState141 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState141 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState141

and _menhir_run129 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState129

and _menhir_run131 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.pexpr_loc) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState131

and _menhir_goto_constrs : _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * Ast.ptyp option) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState233 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_1 : ((string * Ast.ptyp option) list)) = _v in
        let _v : (Ast.ptyp) = 
# 222 "parser.mly"
              (PTConstrs _1)
# 4387 "parser.ml"
         in
        _menhir_goto_type_def _menhir_env _menhir_stack _menhir_s _v
    | MenhirState240 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_3 : ((string * Ast.ptyp option) list)) = _v in
        let (_menhir_stack, _menhir_s, (_1 : (string * Ast.ptyp option))) = _menhir_stack in
        let _2 = () in
        let _v : ((string * Ast.ptyp option) list) = 
# 218 "parser.mly"
                               (_1 :: _3)
# 4399 "parser.ml"
         in
        _menhir_goto_constrs _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_var_type_list : _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * Ast.ptyp) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState261 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 4415 "parser.ml"
        )), _startpos__1_), _, (_3 : (Ast.ptyp))), _endpos__4_, _), _, (_5 : ((string * Ast.ptyp) list))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _v : ((string * Ast.ptyp) list) = 
# 179 "parser.mly"
                                             ((_1, _3)::_5)
# 4422 "parser.ml"
         in
        _menhir_goto_var_type_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState257 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB3 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let ((_menhir_stack, _startpos__2_), _, (_3 : ((string * Ast.ptyp) list))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Ast.ptyp) = 
# 175 "parser.mly"
                                    (PTRecord (_3))
# 4443 "parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (x : (Ast.ptyp)) = _v in
            let _v : (Ast.ptyp option) = 
# 102 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( Some x )
# 4451 "parser.ml"
             in
            _menhir_goto_option_var_decl_ _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_type_def : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ptyp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (t : (Ast.ptyp)) = _v in
    let (((_menhir_stack, _menhir_s), _endpos_id_, (id : (
# 39 "parser.mly"
       (string)
# 4471 "parser.ml"
    )), _startpos_id_), _, (args : (string list))) = _menhir_stack in
    let _4 = () in
    let _1 = () in
    let _v : (unit) = 
# 89 "parser.mly"
                                                                  (
            (* print_endline ("declared type: "^id^": "^(Print.str_ptyp t)); *)
            Hashtbl.add symbol_tbl id (UDT, PTyp (erase_type_args t args))
        )
# 4481 "parser.ml"
     in
    _menhir_goto_declare _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_nonempty_list_str_typ_ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * Ast.ptyp) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (string * Ast.ptyp))), _, (xs : ((string * Ast.ptyp) list))) = _menhir_stack in
        let _v : ((string * Ast.ptyp) list) = 
# 197 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 4496 "parser.ml"
         in
        _menhir_goto_nonempty_list_str_typ_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB3 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (str_pts : ((string * Ast.ptyp) list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : ((string * Ast.ptyp) list) = 
# 246 "parser.mly"
                                                     (str_pts)
# 4516 "parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : ((string * Ast.ptyp) list)) = _v in
            let _v : (Ast.ptyp) = 
# 237 "parser.mly"
                 (PTRecord _1)
# 4524 "parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_tuple_typ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ptyp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, (_1 : (Ast.ptyp))), _), _, (_3 : (Ast.ptyp list))) = _menhir_stack in
        let _2 = () in
        let _v : (Ast.ptyp list) = 
# 243 "parser.mly"
                          (_1 :: _3)
# 4548 "parser.ml"
         in
        _menhir_goto_tuple_typ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (_2 : (Ast.ptyp list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.ptyp) = 
# 236 "parser.mly"
                        (PTTuple _2)
# 4568 "parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run23 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.ptyp) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState23 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TAray ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | TBool ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | TFloat ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | TInt ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | TLst ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | TUnt ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState23
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23

and _menhir_run16 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.ptyp) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState16 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TAray ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | TBool ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | TFloat ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | TInt ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | TLst ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | TUnt ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16

and _menhir_goto_list_typ_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ptyp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState15 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (Ast.ptyp list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (Ast.ptyp))) = _menhir_stack in
        let _v : (Ast.ptyp list) = 
# 187 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 4649 "parser.ml"
         in
        _menhir_goto_list_typ_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (tl : (Ast.ptyp list)) = _v in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 4659 "parser.ml"
        )), _startpos__1_) = _menhir_stack in
        let _v : (Ast.ptyp) = 
# 235 "parser.mly"
                          (PTUdt (_1, tl))
# 4664 "parser.ml"
         in
        _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run161 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 4673 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Dot ->
        _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
    | Add | AddDot | Ando | At | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LArrow | LB2 | LE | LT | Minus | MinusDot | Model | Mult | MultDot | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical | With ->
        _menhir_reduce24 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce143 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : ((string * Ast.pexpr_loc) list) = 
# 389 "parser.mly"
                ([])
# 4696 "parser.ml"
     in
    _menhir_goto_str_expr_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_run79 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 4703 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Equal ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | False ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Float _v ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState80 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | For ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Iden _v ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState80 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | If ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Int _v ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState80 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB2 ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB3 ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Let ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Match ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Negb ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | True ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | UIden _v ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState80 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | While ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce68 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Ast.pexpr_loc list) = 
# 384 "parser.mly"
                    ([])
# 4765 "parser.ml"
     in
    _menhir_goto_expr_single_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_run84 : _menhir_env -> 'ttv_tail * _menhir_state * Lexing.position -> Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__2_ = _endpos in
    let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
    let _2 = () in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__2_ in
    let _v : (Ast.pexpr_loc) = 
# 270 "parser.mly"
                (mk_pexpr_loc PUnt (PTUnt) _startpos__1_ _endpos__2_)
# 4782 "parser.ml"
     in
    _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_reduce24 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (
# 39 "parser.mly"
       (string)
# 4789 "parser.ml"
) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_id_, _menhir_s, (id : (
# 39 "parser.mly"
       (string)
# 4795 "parser.ml"
    )), _startpos_id_) = _menhir_stack in
    let _startpos = _startpos_id_ in
    let _endpos = _endpos_id_ in
    let _v : (string list) = 
# 262 "parser.mly"
                     ([id])
# 4802 "parser.ml"
     in
    _menhir_goto_expr_path _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run160 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (
# 39 "parser.mly"
       (string)
# 4809 "parser.ml"
) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run161 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState160 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState160

and _menhir_goto_expr_single : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Ast.pexpr_loc) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | DotDot ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState143 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState143 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState143 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState143 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState102 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | Semicolon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let (((_menhir_stack, _menhir_s, (_1 : ((string * Ast.pexpr_loc) list))), _endpos__2_, (_2 : (
# 39 "parser.mly"
       (string)
# 4968 "parser.ml"
            )), _startpos__2_), _endpos__4_, _, (_4 : (Ast.pexpr_loc)), _startpos__4_) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _v : ((string * Ast.pexpr_loc) list) = 
# 391 "parser.mly"
                                                       ((_2, _4) :: _1)
# 4975 "parser.ml"
             in
            _menhir_goto_str_expr_list _menhir_env _menhir_stack _menhir_s _v
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | Model | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 304 "parser.mly"
                                             (
            mk_pexpr_loc (POp ("||", [e1;e2])) PTBool _startpos_e1_ _endpos_e2_
        )
# 5038 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | GE | GT | LE | LT | Model | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 332 "parser.mly"
                                                  (mk_pexpr_loc (POp ("!=", [e1;e2])) PTBool _startpos_e1_ _endpos_e2_)
# 5081 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState109 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Add | AddDot | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LE | LT | Minus | MinusDot | Model | Mult | MultDot | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 328 "parser.mly"
                                                (
            mk_pexpr_loc (POp ("*.", [e1;e2])) PTFloat _startpos_e1_ _endpos_e2_
        )
# 5114 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState111 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | RB2 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _startpos__2_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos__4_ in
            let _v : (Ast.pexpr_loc) = 
# 373 "parser.mly"
                                                (
        let e:Ast.pexpr_loc = e1 in
        let et1 = e.ptyp in
        match et1 with
        | PTAray pt -> mk_pexpr_loc (POp ("[]", [e1; e2])) pt _startpos_e1_ _endpos__4_
        | PTVar _ -> mk_pexpr_loc (POp ("[]", [e1; e2])) (PTVar (new_type_var ())) _startpos_e1_ _endpos__4_
        | _ -> raise (Type_mismatch (e1, et1, (PTAray (PTVar (new_type_var())))))        
        )
# 5185 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState114 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Add | AddDot | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LE | LT | Minus | MinusDot | Model | Mult | MultDot | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 319 "parser.mly"
                                             (
            mk_pexpr_loc (POp ("*", [e1;e2])) PTInt _startpos_e1_ _endpos_e2_
        )
# 5220 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Colon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | Model | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 352 "parser.mly"
                                                  (mk_pexpr_loc (PAssign (e1, e2)) (PTUnt) _startpos_e1_ _endpos_e2_)
# 5281 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Add | AddDot | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LE | LT | Minus | MinusDot | Model | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _startpos__2_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 325 "parser.mly"
                                                 (
            mk_pexpr_loc (POp ("-.", [e1;e2])) PTFloat _startpos_e1_ _endpos_e2_
        )
# 5318 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Add | AddDot | Ando | At | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LE | LT | Minus | MinusDot | Model | Mult | MultDot | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 370 "parser.mly"
                                           (
            mk_pexpr_loc (POp ("@", [e1; e2])) e1.ptyp _startpos_e1_ _endpos_e2_
        )
# 5349 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState123 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Add | AddDot | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LE | LT | Minus | MinusDot | Model | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _startpos__2_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 316 "parser.mly"
                                              (
            mk_pexpr_loc (POp ("-", [e1;e2])) PTInt _startpos_e1_ _endpos_e2_
        )
# 5386 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState125 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | Model | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 333 "parser.mly"
                                              (mk_pexpr_loc (POp ("<", [e1;e2])) PTBool _startpos_e1_ _endpos_e2_)
# 5433 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | GE | GT | LE | LT | Model | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 331 "parser.mly"
                                              (mk_pexpr_loc (POp ("=", [e1;e2])) PTBool _startpos_e1_ _endpos_e2_)
# 5476 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Add | AddDot | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LE | LT | Model | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 322 "parser.mly"
                                               (
            mk_pexpr_loc (POp ("+.", [e1;e2])) PTFloat _startpos_e1_ _endpos_e2_
        )
# 5517 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Add | AddDot | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LE | LT | Model | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 313 "parser.mly"
                                            (
            mk_pexpr_loc (POp ("+", [e1;e2])) PTInt _startpos_e1_ _endpos_e2_
        )
# 5558 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | Model | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 335 "parser.mly"
                                              (mk_pexpr_loc (POp ("<=", [e1;e2])) PTBool _startpos_e1_ _endpos_e2_)
# 5605 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState135 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | Model | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 334 "parser.mly"
                                              (mk_pexpr_loc (POp (">", [e1;e2])) PTBool _startpos_e1_ _endpos_e2_)
# 5652 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState137 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | Model | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 336 "parser.mly"
                                              (mk_pexpr_loc (POp (">=", [e1;e2])) PTBool _startpos_e1_ _endpos_e2_)
# 5699 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Add | AddDot | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LE | LT | Minus | MinusDot | Model | Mult | MultDot | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 367 "parser.mly"
                                                                   (
            mk_pexpr_loc (POp ("::", [e1; e2])) e2.ptyp _startpos_e1_ _endpos_e2_
        )
# 5732 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState141 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | Model | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_) = _menhir_stack in
            let _2 = () in
            let _startpos = _startpos_e1_ in
            let _endpos = _endpos_e2_ in
            let _v : (Ast.pexpr_loc) = 
# 301 "parser.mly"
                                              (
            mk_pexpr_loc (POp ("&&", [e1; e2])) PTBool _startpos_e1_ _endpos_e2_ 
        )
# 5791 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | RB2 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Do ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | False ->
                    _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Float _v ->
                    _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | For ->
                    _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Iden _v ->
                    _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | If ->
                    _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Int _v ->
                    _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB1 ->
                    _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB2 ->
                    _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB3 ->
                    _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Let ->
                    _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Match ->
                    _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Minus ->
                    _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | MinusDot ->
                    _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Negb ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | True ->
                    _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | UIden _v ->
                    _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState146 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | While ->
                    _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState146)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState226 | MenhirState214 | MenhirState203 | MenhirState180 | MenhirState176 | MenhirState166 | MenhirState164 | MenhirState146 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | Semicolon ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Colon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | Model | RB1 | RB2 | RB3 | Then | Value | Vertical ->
            _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState171 | MenhirState151 | MenhirState148 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | Semicolon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState151 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState151 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState151 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState151 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState151)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Colon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | Model | RB1 | RB2 | RB3 | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_x_, _menhir_s, (x : (Ast.pexpr_loc)), _startpos_x_) = _menhir_stack in
            let _endpos = _endpos_x_ in
            let _v : (Ast.pexpr_loc list) = 
# 215 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( [ x ] )
# 6053 "parser.ml"
             in
            _menhir_goto_separated_nonempty_list_Semicolon_expr_single_ _menhir_env _menhir_stack _endpos _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState158 | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState158 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState158)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_x_, _menhir_s, (x : (Ast.pexpr_loc)), _startpos_x_) = _menhir_stack in
            let _startpos = _startpos_x_ in
            let _endpos = _endpos_x_ in
            let _v : (Ast.pexpr_loc list) = 
# 215 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( [ x ] )
# 6156 "parser.ml"
             in
            _menhir_goto_separated_nonempty_list_Comma_expr_single_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState87 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | Then ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState164 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState164)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | RB1 ->
            _menhir_run174 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p
        | Semicolon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState171)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | RB1 ->
            _menhir_run174 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p
        | Semicolon ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState81 | MenhirState187 | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | Semicolon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RB2 | Vertical ->
                _menhir_reduce68 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState187)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | RB2 | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Ast.pexpr_loc)), _startpos__1_) = _menhir_stack in
            let _v : (Ast.pexpr_loc list) = 
# 385 "parser.mly"
                    ([_1])
# 6506 "parser.ml"
             in
            _menhir_goto_expr_single_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState80 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | Semicolon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let ((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 6565 "parser.ml"
            )), _startpos__1_), _endpos__3_, _, (_3 : (Ast.pexpr_loc)), _startpos__3_) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : ((string * Ast.pexpr_loc) list) = 
# 390 "parser.mly"
                                       ([(_1, _3)])
# 6572 "parser.ml"
             in
            _menhir_goto_str_expr_list _menhir_env _menhir_stack _menhir_s _v
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | GE | GT | LE | LT | Model | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s, _startpos__1_), _endpos_p_, _, (p : (Ast.ppattern_loc)), _startpos_p_), _), _endpos_e_, _, (e : (Ast.pexpr_loc)), _startpos_e_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_e_ in
            let _v : (Ast.pexpr_loc) = 
# 366 "parser.mly"
                                            (mk_pexpr_loc (PLet (p, e)) PTUnt _startpos__1_ _endpos_e_)
# 6618 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LB3 ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Vertical ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let x = () in
                let _v : (unit option) = 
# 102 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( Some x )
# 6683 "parser.ml"
                 in
                _menhir_goto_option_Vertical_ _menhir_env _menhir_stack _v
            | Float _ | Iden _ | Int _ | LB1 | LB2 | UIden _ | Underline ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _v : (unit option) = 
# 100 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( None )
# 6691 "parser.ml"
                 in
                _menhir_goto_option_Vertical_ _menhir_env _menhir_stack _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Add | AddDot | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LE | LT | Minus | MinusDot | Model | Mult | MultDot | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (Ast.pexpr_loc)), _startpos_e_) = _menhir_stack in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_e_ in
            let _v : (Ast.pexpr_loc) = 
# 307 "parser.mly"
                                       (
            mk_pexpr_loc (POp ("-", [e])) PTInt _startpos__1_ _endpos_e_
        )
# 6730 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Add | AddDot | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LE | LT | Minus | MinusDot | Model | Mult | MultDot | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (Ast.pexpr_loc)), _startpos_e_) = _menhir_stack in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_e_ in
            let _v : (Ast.pexpr_loc) = 
# 310 "parser.mly"
                                          (
            mk_pexpr_loc (POp ("-.", [e])) PTFloat _startpos__1_ _endpos_e_
        )
# 6763 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Ando | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | Model | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : (Ast.pexpr_loc)), _startpos_e_) = _menhir_stack in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_e_ in
            let _v : (Ast.pexpr_loc) = 
# 298 "parser.mly"
                               (
            mk_pexpr_loc (POp ("!", [e])) PTBool _startpos__1_ _endpos_e_
        )
# 6820 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState41 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Colon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Function | Model | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_uid_, _menhir_s, (uid : (
# 39 "parser.mly"
       (string)
# 6877 "parser.ml"
            )), _startpos_uid_), _endpos_e_, _, (e : (Ast.pexpr_loc)), _startpos_e_) = _menhir_stack in
            let _startpos = _startpos_uid_ in
            let _endpos = _endpos_e_ in
            let _v : (Ast.pexpr_loc) = 
# 356 "parser.mly"
                                  (
            mk_pexpr_loc (PConstr ((PConstr_compound (uid, e)))) (PTVar (new_type_var ())) _startpos_uid_ _endpos_e_
        )
# 6886 "parser.ml"
             in
            _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Do ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState214)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | Datatype | EOF | Function | Model | Value ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s), _endpos_id_, (id : (
# 39 "parser.mly"
       (string)
# 7035 "parser.ml"
            )), _startpos_id_), _, (ote : (Ast.ptyp option))), _endpos_e_, _, (e : (Ast.pexpr_loc)), _startpos_e_) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _v : (unit) = 
# 93 "parser.mly"
                                                                         (
            (* print_endline ("declared value "^id); *)
            match ote with
            | None -> Hashtbl.add symbol_tbl id (Val, PExpr_loc (PTVar (new_type_var ()), e))
            | Some pt -> Hashtbl.add symbol_tbl id (Val, PExpr_loc (pt, e))
        )
# 7047 "parser.ml"
             in
            _menhir_goto_declare _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState270 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | Semicolon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run269 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState272 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RB3 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 7111 "parser.ml"
                )), _startpos__1_), _endpos__3_, _, (_3 : (Ast.pexpr_loc)), _startpos__3_), _endpos__4_) = _menhir_stack in
                let _4 = () in
                let _2 = () in
                let _startpos = _startpos__1_ in
                let _endpos = _endpos__4_ in
                let _v : ((string * Ast.pexpr_loc) list) = 
# 171 "parser.mly"
                                                ([(_1, _3)])
# 7120 "parser.ml"
                 in
                _menhir_goto_var_expr_list _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState272)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState281 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | Colon ->
            _menhir_run286 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | Semicolon ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | RB3 ->
            _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState286 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | Semicolon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState288 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState288 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState288 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState288 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState288 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RB3 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _endpos_e1_, _menhir_s, (e1 : (Ast.pexpr_loc)), _startpos_e1_), _endpos_e2_, _, (e2 : (Ast.pexpr_loc)), _startpos_e2_), _endpos__4_) = _menhir_stack in
                let _4 = () in
                let _2 = () in
                let _v : ((Ast.pexpr_loc * Ast.pexpr_loc) list) = 
# 187 "parser.mly"
                                                                    ([(e1, e2)])
# 7280 "parser.ml"
                 in
                _menhir_goto_transition_items _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState288)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState288 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | Colon ->
            _menhir_run286 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState302 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Add ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | AddDot ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack)
        | Ando ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | At ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | ColonColon ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
        | GE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | LArrow ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | LB2 ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack)
        | Minus ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Mult ->
            _menhir_run114 _menhir_env (Obj.magic _menhir_stack)
        | MultDot ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack)
        | Non_Equal ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | Oro ->
            _menhir_run105 _menhir_env (Obj.magic _menhir_stack)
        | Semicolon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run295 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState304 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RB3 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((((((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 7401 "parser.ml"
                )), _startpos__1_), _startpos__2_), _, (_3 : (string list))), _endpos__4_), _endpos_e_, _, (e : (Ast.pexpr_loc)), _startpos_e_), _endpos__7_) = _menhir_stack in
                let _7 = () in
                let _5 = () in
                let _4 = () in
                let _2 = () in
                let _v : ((string * (string list * Ast.pexpr_loc)) list) = 
# 157 "parser.mly"
                                                                               ([(_1, (_3, e))])
# 7410 "parser.ml"
                 in
                _menhir_goto_atomic_def_list _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState304)
        | With ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_constr : _menhir_env -> 'ttv_tail -> _menhir_state -> (string * Ast.ptyp option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Vertical ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | UIden _v ->
            _menhir_run234 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState240 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState240)
    | Datatype | EOF | Function | Model | Value ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (c : (string * Ast.ptyp option))) = _menhir_stack in
        let _v : ((string * Ast.ptyp option) list) = 
# 217 "parser.mly"
                    ([c])
# 7452 "parser.ml"
         in
        _menhir_goto_constrs _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_option_init_decl_ : _menhir_env -> 'ttv_tail -> (Ast.pexpr_loc option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Transition ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LB3 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Next ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | Float _v ->
                    _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState279 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Iden _v ->
                    _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState279 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Int _v ->
                    _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState279 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB1 ->
                    _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState279 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB2 ->
                    _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState279 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | UIden _v ->
                    _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState279 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Underline ->
                    _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState279 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState279)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run269 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 7523 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Equal ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | False ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Float _v ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState270 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | For ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Iden _v ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState270 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | If ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Int _v ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState270 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB2 ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB3 ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Let ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Match ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Negb ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | True ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | UIden _v ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState270 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | While ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState270)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_typ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ptyp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState15 | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | Iden _v ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState15 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState15 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB3 ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState15 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TAray ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | TBool ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | TFloat ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | TInt ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | TLst ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | TUnt ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | Comma | Datatype | EOF | Equal | Function | Model | RB1 | Semicolon | Value | Vertical ->
            _menhir_reduce93 _menhir_env (Obj.magic _menhir_stack) MenhirState15
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState15)
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState17
        | Comma | Datatype | EOF | Equal | Function | Iden _ | LB1 | LB3 | Model | RB1 | Semicolon | TAray | TBool | TFloat | TInt | TLst | TUnt | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (_1 : (Ast.ptyp))), _), _, (_3 : (Ast.ptyp))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.ptyp) = 
# 238 "parser.mly"
                    (PTArrow (_1, _3))
# 7629 "parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17)
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | Comma ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState21
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState21 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (t : (Ast.ptyp))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.ptyp) = 
# 239 "parser.mly"
                        (t)
# 7658 "parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState21)
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | Comma ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (_1 : (Ast.ptyp))), _), _, (_3 : (Ast.ptyp))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.ptyp list) = 
# 242 "parser.mly"
                         ([_1; _3])
# 7681 "parser.ml"
             in
            _menhir_goto_tuple_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24)
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Semicolon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState28 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let ((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 7705 "parser.ml"
            )), _startpos__1_), _, (_3 : (Ast.ptyp))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : (string * Ast.ptyp) = 
# 249 "parser.mly"
                                  ((_1, _3))
# 7712 "parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState30 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RB3 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (x : (string * Ast.ptyp))) = _menhir_stack in
                let _v : ((string * Ast.ptyp) list) = 
# 195 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( [ x ] )
# 7727 "parser.ml"
                 in
                _menhir_goto_nonempty_list_str_typ_ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState30)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState28)
    | MenhirState9 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | Comma | Datatype | EOF | Equal | Function | Iden _ | LB1 | LB3 | Model | RB1 | Semicolon | TAray | TBool | TFloat | TInt | TLst | TUnt | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (_2 : (Ast.ptyp))) = _menhir_stack in
            let _1 = () in
            let _v : (Ast.ptyp) = 
# 233 "parser.mly"
                (PTAray (_2))
# 7752 "parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34)
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState35
        | Comma | Datatype | EOF | Equal | Function | Iden _ | LB1 | LB3 | Model | RB1 | Semicolon | TAray | TBool | TFloat | TInt | TLst | TUnt | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (_2 : (Ast.ptyp))) = _menhir_stack in
            let _1 = () in
            let _v : (Ast.ptyp) = 
# 234 "parser.mly"
               (PTLst (_2))
# 7773 "parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState35)
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | Equal ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (_2 : (Ast.ptyp))) = _menhir_stack in
            let _1 = () in
            let _v : (Ast.ptyp) = 
# 106 "parser.mly"
                        (_2)
# 7794 "parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (x : (Ast.ptyp)) = _v in
            let _v : (Ast.ptyp option) = 
# 102 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( Some x )
# 7802 "parser.ml"
             in
            _menhir_goto_option_type_of_expr_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36)
    | MenhirState234 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState235
        | Datatype | EOF | Function | Model | Value | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_uid_, _menhir_s, (uid : (
# 39 "parser.mly"
       (string)
# 7821 "parser.ml"
            )), _startpos_uid_), _, (t : (Ast.ptyp))) = _menhir_stack in
            let _v : (string * Ast.ptyp option) = 
# 226 "parser.mly"
                           ((uid, Some t))
# 7826 "parser.ml"
             in
            _menhir_goto_constr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState235)
    | MenhirState233 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState237
        | Datatype | EOF | Function | Model | Value ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (_1 : (Ast.ptyp))) = _menhir_stack in
            let _v : (Ast.ptyp) = 
# 221 "parser.mly"
              (_1)
# 7846 "parser.ml"
             in
            _menhir_goto_type_def _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState237)
    | MenhirState259 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState260
        | Semicolon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState260 in
            let _menhir_stack = (_menhir_stack, _endpos, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run258 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState261 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RB3 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 39 "parser.mly"
       (string)
# 7875 "parser.ml"
                )), _startpos__1_), _, (_3 : (Ast.ptyp))), _endpos__4_, _) = _menhir_stack in
                let _4 = () in
                let _2 = () in
                let _v : ((string * Ast.ptyp) list) = 
# 178 "parser.mly"
                                        ([(_1, _3)])
# 7882 "parser.ml"
                 in
                _menhir_goto_var_type_list _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState261)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState260)
    | _ ->
        _menhir_fail ()

and _menhir_run11 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 7899 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Colon ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState12 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB3 ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TAray ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | TBool ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | TFloat ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | TInt ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | TLst ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | TUnt ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState12
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce93 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Ast.ptyp list) = 
# 185 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 7945 "parser.ml"
     in
    _menhir_goto_list_typ_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_args : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ppattern_loc list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Ast.ppattern_loc)), _startpos__1_), _, (_2 : (Ast.ppattern_loc list))) = _menhir_stack in
        let _v : (Ast.ppattern_loc list) = 
# 110 "parser.mly"
                    (_1 :: _2)
# 7960 "parser.ml"
         in
        _menhir_goto_args _menhir_env _menhir_stack _menhir_s _v
    | MenhirState221 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Colon ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState224
        | Equal ->
            _menhir_reduce107 _menhir_env (Obj.magic _menhir_stack) MenhirState224
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState224)
    | _ ->
        _menhir_fail ()

and _menhir_run85 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RB1 ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState85

and _menhir_run40 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40

and _menhir_run41 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 8074 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Dot ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState41 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState210 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState210)
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Add | AddDot | Ando | At | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LArrow | LE | LT | Model | Mult | MultDot | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical | With ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_uid_, _menhir_s, (uid : (
# 39 "parser.mly"
       (string)
# 8133 "parser.ml"
        )), _startpos_uid_) = _menhir_stack in
        let _startpos = _startpos_uid_ in
        let _endpos = _endpos_uid_ in
        let _v : (Ast.pexpr_loc) = 
# 355 "parser.mly"
                  (mk_pexpr_loc (PConstr ((PConstr_basic uid))) (PTVar (new_type_var ())) _startpos_uid_ _endpos_uid_)
# 8140 "parser.ml"
         in
        _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState41

and _menhir_run42 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Ast.pexpr_loc) = 
# 288 "parser.mly"
            (mk_pexpr_loc (PBool true) (PTBool) _startpos__1_ _endpos__1_)
# 8160 "parser.ml"
     in
    _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run43 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState43 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState43 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState43 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState43 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState43

and _menhir_run44 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44

and _menhir_run45 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState45 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState45 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState45 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState45 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState45

and _menhir_run46 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46

and _menhir_run47 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Float _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState47 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState47 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState47 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState47 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Underline ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState47 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState47

and _menhir_run78 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState78 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RB3 ->
        _menhir_reduce143 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78

and _menhir_run81 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState81 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Vertical ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState81 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | False ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Float _v ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | For ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Iden _v ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | If ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Int _v ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB2 ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB3 ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Let ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Match ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Negb ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | True ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | UIden _v ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | While ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Vertical ->
            _menhir_reduce68 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82)
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RB2 ->
        _menhir_reduce68 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState81

and _menhir_run83 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState83 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState83 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState83 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RB1 ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState83
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState83 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState83

and _menhir_run86 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 37 "parser.mly"
       (int)
# 8528 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_i_ = _endpos in
    let (i : (
# 37 "parser.mly"
       (int)
# 8537 "parser.ml"
    )) = _v in
    let _startpos_i_ = _startpos in
    let _startpos = _startpos_i_ in
    let _endpos = _endpos_i_ in
    let _v : (Ast.pexpr_loc) = 
# 268 "parser.mly"
                (mk_pexpr_loc (PInt i) (PTInt) _startpos_i_ _endpos_i_)
# 8545 "parser.ml"
     in
    _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run87 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | False ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Float _v ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState87 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | For ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState87 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | If ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState87 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Let ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Match ->
        _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Minus ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MinusDot ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Negb ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | True ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState87 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | While ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState87

and _menhir_run88 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 8597 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Dot ->
        _menhir_run160 _menhir_env (Obj.magic _menhir_stack)
    | LB1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | False ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Float _v ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | For ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Iden _v ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | If ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Int _v ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB2 ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB3 ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Let ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Match ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Minus ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | MinusDot ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Negb ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | True ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | UIden _v ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | While ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState89)
    | Add | AddDot | Ando | At | Colon | ColonColon | Comma | Datatype | Do | Done | DotDot | EOF | Else | Equal | Function | GE | GT | LArrow | LB2 | LE | LT | Minus | MinusDot | Model | Mult | MultDot | Non_Equal | Oro | RB1 | RB2 | RB3 | Semicolon | Then | Value | Vertical | With ->
        _menhir_reduce24 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run90 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | In ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LB2 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | False ->
                    _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Float _v ->
                    _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | For ->
                    _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Iden _v ->
                    _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | If ->
                    _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Int _v ->
                    _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB1 ->
                    _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB2 ->
                    _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LB3 ->
                    _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Let ->
                    _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Match ->
                    _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Minus ->
                    _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | MinusDot ->
                    _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | Negb ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | True ->
                    _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | UIden _v ->
                    _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | While ->
                    _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run94 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 38 "parser.mly"
       (float)
# 8746 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_f_ = _endpos in
    let (f : (
# 38 "parser.mly"
       (float)
# 8755 "parser.ml"
    )) = _v in
    let _startpos_f_ = _startpos in
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Ast.pexpr_loc) = 
# 269 "parser.mly"
                (mk_pexpr_loc (PFloat f) (PTFloat) _startpos_f_ _endpos_f_)
# 8763 "parser.ml"
     in
    _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run95 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Ast.pexpr_loc) = 
# 289 "parser.mly"
            (mk_pexpr_loc (PBool false) (PTBool) _startpos__1_ _endpos__1_)
# 8779 "parser.ml"
     in
    _menhir_goto_expr_single _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_pattern_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ppattern_loc list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState51 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RB2 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__5_ = _endpos in
                let (((_menhir_stack, _menhir_s, _startpos__1_), _), _, (pl : (Ast.ppattern_loc list))) = _menhir_stack in
                let _5 = () in
                let _4 = () in
                let _2 = () in
                let _1 = () in
                let _startpos = _startpos__1_ in
                let _endpos = _endpos__5_ in
                let _v : (Ast.ppattern_loc) = 
# 407 "parser.mly"
                                                   (
            match pl with
            | [] -> mk_ppat_loc (PPat_Aray []) (PTAray (PTVar (new_type_var()))) _startpos__1_ _endpos__5_
            | p::pl' -> mk_ppat_loc (PPat_Aray (pl)) (PTAray p.ptyp) _startpos__1_ _endpos__5_
        )
# 8817 "parser.ml"
                 in
                _menhir_goto_pattern _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Ast.ppattern_loc)), _startpos__1_), _endpos__2_, _), _, (_3 : (Ast.ppattern_loc list))) = _menhir_stack in
        let _2 = () in
        let _v : (Ast.ppattern_loc list) = 
# 427 "parser.mly"
                                     (_1 :: _3)
# 8840 "parser.ml"
         in
        _menhir_goto_pattern_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB2 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (pl : (Ast.ppattern_loc list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : (Ast.ppattern_loc) = 
# 412 "parser.mly"
                                  (
            match pl with
            | [] -> mk_ppat_loc (PPat_Lst []) (PTLst (PTVar (new_type_var()))) _startpos__1_ _endpos__3_
            | p::pl' -> mk_ppat_loc (PPat_Lst pl) (PTLst p.ptyp) _startpos__1_ _endpos__3_
        )
# 8866 "parser.ml"
             in
            _menhir_goto_pattern _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_Comma_pattern_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ppattern_loc list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let ((((_menhir_stack, _menhir_s, _startpos__1_), _endpos_p_, _, (p : (Ast.ppattern_loc)), _startpos_p_), _), _, (pl : (Ast.ppattern_loc list))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__5_ in
            let _v : (Ast.ppattern_loc) = 
# 419 "parser.mly"
                                                                               (mk_ppat_loc (PPat_Tuple (p::pl)) (PTTuple (List.map (fun pat -> pat.ptyp) (p::pl))) _startpos__1_ _endpos__5_)
# 8902 "parser.ml"
             in
            _menhir_goto_pattern _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos_x_, _menhir_s, (x : (Ast.ppattern_loc)), _startpos_x_), _), _, (xs : (Ast.ppattern_loc list))) = _menhir_stack in
        let _2 = () in
        let _v : (Ast.ppattern_loc list) = 
# 217 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 8919 "parser.ml"
         in
        _menhir_goto_separated_nonempty_list_Comma_pattern_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run65 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (Ast.ppattern_loc) * Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Float _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState65 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState65 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState65 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState65 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Underline ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState65 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65

and _menhir_run234 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 8953 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TAray ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState234
    | TBool ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState234
    | TFloat ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState234
    | TInt ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState234
    | TLst ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState234
    | TUnt ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState234
    | Datatype | EOF | Function | Model | Value | Vertical ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_uid_, _menhir_s, (uid : (
# 39 "parser.mly"
       (string)
# 8983 "parser.ml"
        )), _startpos_uid_) = _menhir_stack in
        let _v : (string * Ast.ptyp option) = 
# 225 "parser.mly"
                    ((*print_endline ("found constr "^uid);*) (uid, None))
# 8988 "parser.ml"
         in
        _menhir_goto_constr _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState234

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_option_var_decl_ : _menhir_env -> 'ttv_tail -> (Ast.ptyp option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Init ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LB3 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run269 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState268 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState268)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | Transition ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _v : (Ast.pexpr_loc option) = 
# 100 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( None )
# 9036 "parser.ml"
         in
        _menhir_goto_option_init_decl_ _menhir_env _menhir_stack _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run258 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 9048 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Colon ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState259 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB3 ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState259 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TAray ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState259
        | TBool ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState259
        | TFloat ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState259
        | TInt ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState259
        | TLst ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState259
        | TUnt ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState259
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState259)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_program : _menhir_env -> 'ttv_tail -> (
# 45 "parser.mly"
       ((string list) * (Ast.psymbol_tbl) * ((Ast.pkripke_model) option))
# 9092 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_1 : (
# 45 "parser.mly"
       ((string list) * (Ast.psymbol_tbl) * ((Ast.pkripke_model) option))
# 9100 "parser.ml"
    )) = _v in
    Obj.magic _1

and _menhir_goto_option_type_of_expr_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ptyp option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Equal ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState39 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState39 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState39 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState39 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState39)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState224 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Equal ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState226 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState226 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState226 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState226 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState226)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Ast.ptyp) = 
# 232 "parser.mly"
            (PTUnt)
# 9227 "parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState5 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TAray ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | TBool ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | TFloat ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | TInt ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | TLst ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | TUnt ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState5

and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Ast.ptyp) = 
# 229 "parser.mly"
          (PTInt)
# 9268 "parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Ast.ptyp) = 
# 231 "parser.mly"
             (PTFloat)
# 9280 "parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Ast.ptyp) = 
# 230 "parser.mly"
            (PTBool)
# 9292 "parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState9 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TAray ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | TBool ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | TFloat ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | TInt ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | TLst ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | TUnt ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState9

and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState10 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState10

and _menhir_run13 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState13 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TAray ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | TBool ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | TFloat ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | TInt ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | TLst ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | TUnt ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState13

and _menhir_run14 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 9370 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState14 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState14 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState14 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TAray ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState14
    | TBool ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState14
    | TFloat ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState14
    | TInt ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState14
    | TLst ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState14
    | TUnt ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState14
    | Arrow | Comma | Datatype | EOF | Equal | Function | Model | RB1 | Semicolon | Value | Vertical ->
        _menhir_reduce93 _menhir_env (Obj.magic _menhir_stack) MenhirState14
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14

and _menhir_reduce126 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Ast.ppattern_loc list) = 
# 425 "parser.mly"
                ([])
# 9407 "parser.ml"
     in
    _menhir_goto_pattern_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_pattern : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Ast.ppattern_loc) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ColonColon ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState57 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Float _v ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Underline ->
                _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59)
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState57 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Ast.ppattern_loc)), _startpos__2_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : (Ast.ppattern_loc) = 
# 422 "parser.mly"
                        (_2)
# 9462 "parser.ml"
             in
            _menhir_goto_pattern _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState57)
    | MenhirState63 | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ColonColon ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | Comma ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState62 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Float _v ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState63 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState63 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState63 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState63 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Underline ->
                _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63)
        | RB1 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_x_, _menhir_s, (x : (Ast.ppattern_loc)), _startpos_x_) = _menhir_stack in
            let _v : (Ast.ppattern_loc list) = 
# 215 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( [ x ] )
# 9507 "parser.ml"
             in
            _menhir_goto_separated_nonempty_list_Comma_pattern_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62)
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _endpos_p1_, _menhir_s, (p1 : (Ast.ppattern_loc)), _startpos_p1_), _), _endpos_p2_, _, (p2 : (Ast.ppattern_loc)), _startpos_p2_) = _menhir_stack in
        let _2 = () in
        let _startpos = _startpos_p1_ in
        let _endpos = _endpos_p2_ in
        let _v : (Ast.ppattern_loc) = 
# 417 "parser.mly"
                                                              (mk_ppat_loc (PPat_Lst_Cons (p1, p2)) (p2.ptyp) _startpos_p1_ _endpos_p2_)
# 9524 "parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState50 | MenhirState71 | MenhirState51 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ColonColon ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | Semicolon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState70 in
            let _menhir_stack = (_menhir_stack, _endpos, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Float _v ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Underline ->
                _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RB2 | Vertical ->
                _menhir_reduce126 _menhir_env (Obj.magic _menhir_stack) MenhirState71
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71)
        | RB2 | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Ast.ppattern_loc)), _startpos__1_) = _menhir_stack in
            let _v : (Ast.ppattern_loc list) = 
# 426 "parser.mly"
                ([_1])
# 9568 "parser.ml"
             in
            _menhir_goto_pattern_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState70)
    | MenhirState49 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ColonColon ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | Arrow | Assigno | Colon | Comma | Equal | Float _ | Iden _ | Int _ | LB1 | LB2 | RB1 | RB2 | Semicolon | UIden _ | Underline | Vertical ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _endpos_uid_, _menhir_s, (uid : (
# 39 "parser.mly"
       (string)
# 9587 "parser.ml"
            )), _startpos_uid_), _endpos_p_, _, (p : (Ast.ppattern_loc)), _startpos_p_) = _menhir_stack in
            let _startpos = _startpos_uid_ in
            let _endpos = _endpos_p_ in
            let _v : (Ast.ppattern_loc) = 
# 421 "parser.mly"
                               (mk_ppat_loc (PPat_Constr (uid, Some p)) (PTVar (new_type_var())) _startpos_uid_ _endpos_p_)
# 9594 "parser.ml"
             in
            _menhir_goto_pattern _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75)
    | MenhirState47 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ColonColon ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | Equal ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState76 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState77 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState76)
    | MenhirState205 | MenhirState200 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState202 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState203 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState203 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState203 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState203 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState203)
        | ColonColon ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState202
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState202)
    | MenhirState222 | MenhirState221 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ColonColon ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState222
        | Float _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState222 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Iden _v ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState222 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Int _v ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState222 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB2 ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | UIden _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState222 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Underline ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState222 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Colon | Equal ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Ast.ppattern_loc)), _startpos__1_) = _menhir_stack in
            let _v : (Ast.ppattern_loc list) = 
# 109 "parser.mly"
              ([_1])
# 9740 "parser.ml"
             in
            _menhir_goto_args _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState222)
    | MenhirState279 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Assigno ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState280 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | False ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Float _v ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState281 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | For ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Iden _v ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState281 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | If ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Int _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState281 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB2 ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Let ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Match ->
                _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Minus ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | MinusDot ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | Negb ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | True ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UIden _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState281 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | While ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState281 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState281)
        | ColonColon ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState280
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState280)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_Iden_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (string list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState230 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 39 "parser.mly"
       (string)
# 9816 "parser.ml"
        )), _startpos_x_), _, (xs : (string list))) = _menhir_stack in
        let _v : (string list) = 
# 187 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 9821 "parser.ml"
         in
        _menhir_goto_list_Iden_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState229 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Equal ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Iden _v ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState233 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB1 ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LB3 ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TAray ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | TBool ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | TFloat ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | TInt ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | TLst ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | TUnt ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | UIden _v ->
                _menhir_run234 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState233 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState233)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_declars : _menhir_env -> 'ttv_tail -> _menhir_state -> (unit) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState247 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, (_1 : (unit))), _, (_2 : (unit))) = _menhir_stack in
            let _3 = () in
            let _v : (
# 45 "parser.mly"
       ((string list) * (Ast.psymbol_tbl) * ((Ast.pkripke_model) option))
# 9884 "parser.ml"
            ) = 
# 75 "parser.mly"
                               (!imported, symbol_tbl, None)
# 9888 "parser.ml"
             in
            _menhir_goto_program _menhir_env _menhir_stack _v
        | Model ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | UIden _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LB1 ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_stack = (_menhir_stack, _startpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | RB1 ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                        let _menhir_stack = (_menhir_stack, _endpos) in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | LB3 ->
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                            let _menhir_stack = (_menhir_stack, _startpos) in
                            let _menhir_env = _menhir_discard _menhir_env in
                            let _tok = _menhir_env._menhir_token in
                            (match _tok with
                            | Var ->
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let _menhir_env = _menhir_discard _menhir_env in
                                let _tok = _menhir_env._menhir_token in
                                (match _tok with
                                | LB3 ->
                                    let _menhir_stack = Obj.magic _menhir_stack in
                                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                                    let _menhir_stack = (_menhir_stack, _startpos) in
                                    let _menhir_env = _menhir_discard _menhir_env in
                                    let _tok = _menhir_env._menhir_token in
                                    (match _tok with
                                    | Iden _v ->
                                        _menhir_run258 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                                    | _ ->
                                        assert (not _menhir_env._menhir_error);
                                        _menhir_env._menhir_error <- true;
                                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState257)
                                | _ ->
                                    assert (not _menhir_env._menhir_error);
                                    _menhir_env._menhir_error <- true;
                                    let _menhir_stack = Obj.magic _menhir_stack in
                                    raise _eRR)
                            | Init | Transition ->
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let _v : (Ast.ptyp option) = 
# 100 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( None )
# 9953 "parser.ml"
                                 in
                                _menhir_goto_option_var_decl_ _menhir_env _menhir_stack _v
                            | _ ->
                                assert (not _menhir_env._menhir_error);
                                _menhir_env._menhir_error <- true;
                                let _menhir_stack = Obj.magic _menhir_stack in
                                raise _eRR)
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            let _menhir_stack = Obj.magic _menhir_stack in
                            raise _eRR)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        raise _eRR)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    raise _eRR)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState407 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (_1 : (unit))), _, (_2 : (unit))) = _menhir_stack in
        let _v : (unit) = 
# 86 "parser.mly"
                      ()
# 9994 "parser.ml"
         in
        _menhir_goto_declars _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_reduce107 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Ast.ptyp option) = 
# 100 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( None )
# 10005 "parser.ml"
     in
    _menhir_goto_option_type_of_expr_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB3 ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TAray ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | TBool ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | TFloat ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | TInt ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | TLst ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | TUnt ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3

and _menhir_run48 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Ast.ppattern_loc) = 
# 418 "parser.mly"
                    (mk_ppat_loc PPat_Underline (PTVar (new_type_var())) _startpos__1_ _endpos__1_)
# 10050 "parser.ml"
     in
    _menhir_goto_pattern _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run49 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 10057 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Float _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState49 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState49 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState49 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState49 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Underline ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState49 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Arrow | Assigno | Colon | ColonColon | Comma | Equal | RB1 | RB2 | Semicolon | Vertical ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos_uid_, _menhir_s, (uid : (
# 39 "parser.mly"
       (string)
# 10083 "parser.ml"
        )), _startpos_uid_) = _menhir_stack in
        let _startpos = _startpos_uid_ in
        let _endpos = _endpos_uid_ in
        let _v : (Ast.ppattern_loc) = 
# 420 "parser.mly"
                  (mk_ppat_loc (PPat_Constr (uid, None)) (PTVar (new_type_var())) _startpos_uid_ _endpos_uid_)
# 10090 "parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49

and _menhir_run50 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Float _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState50 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState50 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState50 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UIden _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState50 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Underline ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState50 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Vertical ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState50 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Float _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState51 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Iden _v ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState51 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Int _v ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState51 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState51 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB2 ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState51 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | UIden _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState51 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Underline ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState51 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Vertical ->
            _menhir_reduce126 _menhir_env (Obj.magic _menhir_stack) MenhirState51
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState51)
    | RB2 ->
        _menhir_reduce126 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50

and _menhir_run52 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Float _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Iden _v ->
        _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Int _v ->
        _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB1 ->
        _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LB2 ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RB1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_s = MenhirState52 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__2_ = _endpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__2_ in
        let _v : (Ast.ppattern_loc) = 
# 406 "parser.mly"
                (mk_ppat_loc (PPat_Unt) PTUnt _startpos__1_ _endpos__2_)
# 10183 "parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | UIden _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Underline ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState52

and _menhir_run54 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 37 "parser.mly"
       (int)
# 10198 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_i_ = _endpos in
    let (i : (
# 37 "parser.mly"
       (int)
# 10207 "parser.ml"
    )) = _v in
    let _startpos_i_ = _startpos in
    let _startpos = _startpos_i_ in
    let _endpos = _endpos_i_ in
    let _v : (Ast.ppattern_loc) = 
# 404 "parser.mly"
                (mk_ppat_loc (PPat_Int i) PTInt _startpos_i_ _endpos_i_)
# 10215 "parser.ml"
     in
    _menhir_goto_pattern _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run55 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 10222 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_id_ = _endpos in
    let (id : (
# 39 "parser.mly"
       (string)
# 10231 "parser.ml"
    )) = _v in
    let _startpos_id_ = _startpos in
    let _startpos = _startpos_id_ in
    let _endpos = _endpos_id_ in
    let _v : (Ast.ppattern_loc) = 
# 403 "parser.mly"
                     (mk_ppat_loc (PPat_Symbol id) (PTVar (new_type_var())) _startpos_id_ _endpos_id_)
# 10239 "parser.ml"
     in
    _menhir_goto_pattern _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run56 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 38 "parser.mly"
       (float)
# 10246 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos_f_ = _endpos in
    let (f : (
# 38 "parser.mly"
       (float)
# 10255 "parser.ml"
    )) = _v in
    let _startpos_f_ = _startpos in
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Ast.ppattern_loc) = 
# 405 "parser.mly"
                (mk_ppat_loc (PPat_Float f) PTFloat _startpos_f_ _endpos_f_)
# 10263 "parser.ml"
     in
    _menhir_goto_pattern _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_reduce89 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (string list) = 
# 185 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 10272 "parser.ml"
     in
    _menhir_goto_list_Iden_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run230 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 39 "parser.mly"
       (string)
# 10279 "parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        _menhir_run230 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState230 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | Equal ->
        _menhir_reduce89 _menhir_env (Obj.magic _menhir_stack) MenhirState230
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState230

and _menhir_reduce18 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (unit) = 
# 85 "parser.mly"
         ()
# 10300 "parser.ml"
     in
    _menhir_goto_declars _menhir_env _menhir_stack _menhir_s _v

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Colon ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | Equal ->
            _menhir_reduce107 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState2)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState407 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState396 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState395 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState394 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState392 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState388 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState383 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState380 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState379 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState376 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState375 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState374 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState373 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState370 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState369 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState366 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState365 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState362 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState361 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState360 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState359 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState356 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState354 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState353 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState352 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState351 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState350 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState346 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s, _), _), _, _, _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState340 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState335 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState331 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s, _), _), _, _, _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState325 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState318 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState315 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState313 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState312 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState310 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState304 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState302 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState298 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState296 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState294 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState288 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState286 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState281 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState280 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState279 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState272 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState270 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState268 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState261 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState260 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState259 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState257 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState247 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState240 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState237 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState235 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState234 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState233 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState230 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState229 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState226 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState224 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState221 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState210 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState205 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState203 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState202 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState200 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState187 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState180 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState176 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState164 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState160 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState158 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState151 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState148 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState146 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState141 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState137 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState135 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState125 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState123 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState114 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState111 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState109 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState102 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState87 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState80 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState76 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState51 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState49 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState47 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState41 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState35 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState28 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState15 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState9 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_goto_debug : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 46 "parser.mly"
        (unit)
# 10949 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_1 : (
# 46 "parser.mly"
        (unit)
# 10957 "parser.ml"
    )) = _v in
    Obj.magic _1

and _menhir_run220 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Float _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState221 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Iden _v ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState221 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Int _v ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState221 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB1 ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState221 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LB2 ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState221 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | UIden _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState221 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Underline ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState221 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState221)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run228 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Iden _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Iden _v ->
            _menhir_run230 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState229 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | Equal ->
            _menhir_reduce89 _menhir_env (Obj.magic _menhir_stack) MenhirState229
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState229)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_imported : _menhir_env -> 'ttv_tail -> (unit) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Datatype ->
        _menhir_run228 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | Function ->
        _menhir_run220 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | Import ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState247 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | UIden _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let (_3 : (
# 39 "parser.mly"
       (string)
# 11057 "parser.ml"
            )) = _v in
            let _startpos__3_ = _startpos in
            let ((_menhir_stack, (_1 : (unit))), _) = _menhir_stack in
            let _2 = () in
            let _v : (unit) = 
# 80 "parser.mly"
                            (print_endline ("imported "^_3); imported := _3 :: !imported)
# 11065 "parser.ml"
             in
            _menhir_goto_imported _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | Value ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | EOF | Model ->
        _menhir_reduce18 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState247

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and _menhir_init : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> _menhir_env =
  fun lexer lexbuf ->
    let _tok = Obj.magic () in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and debug : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 46 "parser.mly"
        (unit)
# 11108 "parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = _menhir_init lexer lexbuf in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Datatype ->
        _menhir_run228 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Function ->
        _menhir_run220 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Import ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | UIden _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__2_ = _endpos in
            let (_2 : (
# 39 "parser.mly"
       (string)
# 11136 "parser.ml"
            )) = _v in
            let _startpos__2_ = _startpos in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            let _1 = () in
            let _v : (
# 46 "parser.mly"
        (unit)
# 11144 "parser.ml"
            ) = 
# 71 "parser.mly"
                   (print_endline ("imported "^_2))
# 11148 "parser.ml"
             in
            _menhir_goto_debug _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | Value ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

and program : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 45 "parser.mly"
       ((string list) * (Ast.psymbol_tbl) * ((Ast.pkripke_model) option))
# 11167 "parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = _menhir_init lexer lexbuf in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (unit) = 
# 79 "parser.mly"
            ()
# 11177 "parser.ml"
     in
    _menhir_goto_imported _menhir_env _menhir_stack _v)

# 430 "parser.mly"
  
# 11183 "parser.ml"

# 219 "/Users/liujian/.opam/system/lib/menhir/standard.mly"
  


# 11189 "parser.ml"
