fun prn (str: string): unit = TextIO.output (TextIO.stdOut, str ^ "\n")

(* Fundamentals
 * ============
 * claim    links an identifier and a type
 * alias    links an identifier and a value
 * prim     creates a new pimitive value (also for pattern matching)\
 * sum      creates a new sum type
 * prod     creates a new prod type
 * lambda   creates a new function
 * ->       creates a new function type
 * =        equality ("unwrap" all the definitions)
 * :        bind a name at the type level to a parameter
*)

structure Source = struct
    type t = {
        buf : string,
        pos : int ref
        marks : (string * int) list ref
    }

    fun eof (buf: t): bool = 
        (String.size (#buf buf) <= 0) orelse (String.size (#buf buf) <= !(#pos buf))
    fun pos (buf: t): int = !(#pos buf)
    fun peek (buf: t): char = String.substring (#buf buf, !(#pos buf))
    fun try_peek (buf: t): char option = 
        if eof buf then NONE else SOME (peek buf)
    fun advance (buf: t): t = ((#pos buf) := !(#pos buf) + 1; buf)
    fun substring (buf: t, i: int, j:int) = String.substring (#buf buf, i, j)

    fun start (buf: t, msg: string): unit = 
        (#marks buf) := (msg, !(#pos buf)) :: !(#marks buf)
    fun success (buf: t) unit = 
        let var marks = #marks buf
        in marks := (case !marks of
            [] => []
            (m::ms) => ms)
        end


    fun fromString (str: string): t = 
        { buf = str, pos = ref 0, marks = ref [] }
    fun fromStream (ss: TextIO.instream): t =
        let val str = TextIO.inputAll ss
        in fromString str
        end
end

structure Parser :> sig
    type expr
    val parseExpr: Source.t -> expr option
    val ppExpr: expr -> string
end = struct
    datatype expr =
        ATOM of string
        LIST of expr vector

    (* todo: some chars can be after the initial pos but not in *)
    fun isAtomChar (c: char): bool = 
        ((c >= #"A") andalso (c <= #"Z")) orelse
        ((c >= #"a") andalso (c <= #"z"))
    fun isWhitespace (c: char): bool = 
        case c of
            #" " => true
            #"\n" => true
            #"\t" => true
            _ => false
    
    fun ppExpr (e: expr): string = 
        case e of
            ATOM s => s
            LIST l => 
            let fun f (e, a) = a ^ " " ^ (ppExpr e)
            in "(" ^ (Vector.foldl f "" l) ^ ")"
            end

    local
        fun parseAtom (buf: Source.t): expr = 
            let 
                val start = Source.pos buf
                fun helper  n = 
                    case Source.try_peek buf of
                    NONE => ATOM (Source.substring (buf, start, n))
                    SOME c =>
                    if isAtomChar c
                    then (Source.advance buf; helper (n + 1))
                    else ATOM (Source.substring (buf, start, i))
            in helper 0
            end

        and parseList (buf: Source.t): expr option = 
            let
                fun helper res = 
                    case Source.try_peek buf of
                        NONE => SOME (LIST (Vector.fromList (List.rev res)))
                        SOME #")" => SOME (LIST (Vector.fromList (List.rev res)))
                        _ => case parseExprHidden buf of
                            NONE => NONE
                            SOME e => helper (e :: res)
            in (Source.advance buf; helper [])
            end

        and parseExprHidden (buf: Source.t): expr option = 
            if Source.eof buf then NONE else
            case Source.peek buf of 
                #"(" => parseList buf
                c => 
                if isWhitespace c then (parseExpr (Source.advance buf)) 
                else if isAtomChar c then SOME (parseAtom buf)
                else NONE
    in
        val parseExpr = parseExprHidden
    end
end

fun main () = 
    let 
        val source = Source.fromStream TextIO.stdIn
        val prog = Parser.parseExpr source
        val repr = case prog of SOME p => Parser.ppExpr p | NONE => "ERROR YOU RETARD!"
    in TextIO.output (TextIO.stdOut, repr ^ "\n")
    end

val _ = main ()