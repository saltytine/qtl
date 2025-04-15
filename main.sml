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
    fun substringstring (buf: t, i: int, j:int) = String.substringstring (#buf buf, i, j)

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

datatype expr =
    ATOM of string
    LIST of expr vector

fun isAtomChar (c: char): bool = (c >= #"A") andalso (c <= #"Z")
fun isWhitespace (c: char): bool = 
    case c of
        #" " => true
        #"\n" => true
        #"\t" => true
        _ => false

fun parseAtom (buf: Source.t): expr = 
    let 
        val start = Source.pos buf
        fun helper  i = (TextIO.output (TextIO.stdOut, (Int.toString i) ^ "\n");
            case Source.try_peek buf of
            NONE => ATOM (Source.substring (buf, start, i))
            SOME c =>
            if isAtomChar c
            then (Source.advance buf; helper (i + 1))
            else ATOM (Source.substring (buf, start, i))
    )
    in helper start
    end

fun parseList (buf: Source.t): expr option = SOME (ATOM "list")

fun parseExpr (buf: Source.t): expr option = 
    if Source.eof buf then NONE else
    case Source.peek buf of 
        #"(" => parseList buf
        c => 
        if isWhitespace c then (parseExpr (Source.advance buf)) 
        else if isAtomChar c then SOME (parseAtom buf)
        else NONE

fun ppExpr (e: expr): string = 
    case e of
        ATOM s => s
        LIST l => 
        let fun f (e, a) = a ^ " " ^ (ppExpr e)
        in "(" ^ (Vector.foldl f "" l) ^ ")"
        end

fun main () = 
    let 
        val source = Source.fromStream TextIO.stdIn
        val prog = parseExpr source
        val repr = case prog of SOME p => ppExpr p | NONE => "ERROR YOU RETARD!"
    in TextIO.output (TextIO.stdOut, repr ^ "\n")
    end

val _ = main ()