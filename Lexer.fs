module Lexer

type Token =
    { Line: int
      Column: int
      Value: string }

type TokenType =
    | Number of Token
    | Let of Token
    | Import of Token
    | String of Token
    | Keyword of Token
    | Go of Token
    | If of Token
    | Else of Token
    | True of Token
    | False of Token
    | Return of Token
    | Match of Token
    | Operator of Token
    | Identifier of Token
    | Assign of Token
    | LBrace of Token
    | RBrace of Token
    | LBracket of Token
    | RBracket of Token
    | Colon of Token
    | LParen of Token
    | RParen of Token
    | Comma of Token
    | Dot of Token
    | Pointer of Token
    | Deref of Token
    | Channel of Token
    | Append of Token
    | PropertyAccess of Token
    | NewLine of Token
    | TypeKeyword of Token
    | Pub of Token
    | Mut of Token
    | Function of Token
    | Equality of Token
    | GT of Token
    | LT of Token
    | GTE of Token
    | LTE of Token
    | EOF of Token
    | And of Token
    | Or of Token
    | Pipe of Token
    | TypeSeparator of Token
    | Range of Token
    | Comment of Token
    | ReturnType of Token
    | ErrorToken of Token

type LexerState =
    { Line: int
      Column: int
      Tokens: TokenType list
      Buffer: char list }

type CharFuncInput =
    | Token of (Token -> TokenType)
    | CharToken
    | IgnoreToken of LexerState

let buildToken state value =
    { Line = state.Line
      Column = state.Column
      Value = value }

let checkNumber (chars) =
    match chars with
    | [] -> false
    | head :: tail ->
        if System.Char.IsDigit head then
            List.forall (fun x -> System.Char.IsDigit x || x = '_') tail
        else
            false

let parseCurrent state =
    let filtered = List.filter (System.Char.IsWhiteSpace >> not) state.Buffer

    match filtered with
    | [] -> state
    | _ ->
        let value = new string (List.toArray <| List.rev state.Buffer)
        let token = buildToken state value

        let t =
            match checkNumber filtered with
            | true -> Number(buildToken state value)
            | false ->
                match value with
                | "if" -> If token
                | "else" -> Else token
                | "let" -> Let token
                | "true" -> True token
                | "false" -> False token
                | "pub" -> Pub token
                | "go" -> Go token
                | "type" -> TypeKeyword token
                | "fn" -> Function token
                | "mut" -> Mut token
                | "return" -> Return token
                | "import" -> Import token
                | "match" -> Match token
                | _ -> Identifier token

        { state with
            Buffer = []
            Tokens = t :: state.Tokens
            Column = state.Column + value.Length }

let checkWhitespace state char =
    let isString =
        match List.tryLast state.Buffer with
        | Some '"' -> true
        | _ -> false

    let parseFunc =
        match isString with
        | true -> id
        | false -> parseCurrent

    let tokenFunc state token =
        match isString with
        | true -> state.Tokens
        | false -> token :: state.Tokens

    let appendBufferFunc thisAcc =
        match isString with
        | true -> char :: thisAcc.Buffer
        | false -> thisAcc.Buffer

    let newState = parseFunc state

    match char, isString with
    | '\n', false
    | '\r', false ->
        { newState with
            Tokens = tokenFunc newState (NewLine(buildToken newState "\n"))
            Buffer = appendBufferFunc newState
            Line = newState.Line + 1
            Column = 1 }
    | ' ', false ->
        { newState with
            Column = newState.Column + 1 }
    | '\t', false ->
        { newState with
            Column = newState.Column + 4 }
    | _ ->
        { state with
            Buffer = char :: state.Buffer }

let charToken state char type' =
    match type' with
    | Token t ->
        Ok(
            { state with
                Tokens = t (buildToken state (char.ToString())) :: state.Tokens
                Column = state.Column + 1
                Buffer = [] }
        )
    | CharToken ->
        Ok
            { state with
                Buffer = char :: state.Buffer }
    | IgnoreToken x -> Ok x


let matchChar char state =
    let newState = parseCurrent state

    charToken
        newState
        char
        (match char with
         | '+'
         | '%'
         | '^'
         | '~' -> Token Operator
         | ',' -> Token Comma
         | '(' -> Token LParen
         | ')' -> Token RParen
         | '{' -> Token LBrace
         | '}' -> Token RBrace
         | '[' -> Token LBracket
         | ']' -> Token RBracket
         | '@' -> Token PropertyAccess
         | ':'
         | '|'
         | '.' -> CharToken
         | _ -> IgnoreToken(checkWhitespace state char))

let quickAppendToken state length token =
    { state with
        Buffer = []
        Tokens = token :: state.Tokens
        Column = state.Column + length }

let (|+>) state (token, offset) = quickAppendToken state offset token


let parseText state char =
    let lastToken = List.tryLast state.Buffer

    match lastToken with
    | Some '"' ->
        (match char with
         | '"' ->
             let token =
                 { Line = state.Line
                   Column = state.Column
                   Value = (List.rev state.Buffer |> List.tail |> List.toArray |> System.String) }

             Ok
                 { state with
                     Tokens = String token :: state.Tokens
                     Buffer = []
                     Column = state.Column + String.length token.Value + 2 }
         | _ ->
             Ok
                 { state with
                     Buffer = char :: state.Buffer })
    | Some '.' ->
        (match char with
         | '.' -> Ok(state |+> (Range(buildToken state ".."), 2))
         | _ -> state |+> (PropertyAccess(buildToken state "."), 1) |> matchChar char)
    | Some '=' ->
        (match char with
         | '=' -> Ok(state |+> (Equality(buildToken state "=="), 2))
         | _ -> state |+> (Assign(buildToken state "="), 1) |> matchChar char)
    | Some '-' ->
        (match char with
         | '>' -> Ok(state |+> (ReturnType(buildToken state "->"), 2))
         | _ -> state |+> (Operator(buildToken state "-"), 1) |> matchChar char)
    | Some '<' ->
        (match char with
         | '=' -> Ok(state |+> (LTE(buildToken state "<="), 2))
         | '-' -> Ok(state |+> (Channel(buildToken state "<-"), 2))
         | _ -> state |+> (LT(buildToken state "<"), 1) |> matchChar char)
    | Some '*' ->
        if System.Char.IsWhiteSpace char then
            state |+> (Operator(buildToken state "*"), 1) |> matchChar char
        else
            state |+> (Deref(buildToken state "*"), 1) |> matchChar char
    | Some '>' ->
        (match char with
         | '=' -> Ok(state |+> (GTE(buildToken state ">="), 2))
         | _ -> state |+> (GT(buildToken state ">"), 1) |> matchChar char)
    | Some '&' ->
        if System.Char.IsWhiteSpace char then
            Error(ErrorToken(buildToken state "&"), "Invalid & character")
        else
            (match char with
             | '&' -> Ok(state |+> (And(buildToken state "&&"), 2))
             | _ -> state |+> (Pointer(buildToken state "&"), 2) |> matchChar char)
    | Some '|' ->
        (match char with
         | '|' -> Ok(state |+> (Or(buildToken state "||"), 2))
         | '>' -> Ok(state |+> (Pipe(buildToken state "|>"), 2))
         | _ -> state |+> (TypeSeparator(buildToken state "|"), 1) |> matchChar char)
    | Some ':' ->
        (match char with
         | ':' -> Ok(state |+> (Append(buildToken state "::"), 2))
         | _ -> state |+> (Colon(buildToken state ":"), 1) |> matchChar char)
    | Some '/' ->
        (match char with
         | '/' -> Ok(state |+> (Comment(buildToken state "//"), 2))
         | _ -> state |+> (Operator(buildToken state "/"), 1) |> matchChar char)
    | _ -> matchChar char state

let lex input =
    let rec lex' state input =
        match input with
        | [] ->
            match List.length state.Buffer with
            | 0 -> Ok state.Tokens
            | _ ->
                let eToken =
                    match List.tryHead state.Tokens with
                    | Some x -> x
                    | None -> ErrorToken <| buildToken state ""

                Error(eToken, "Unexpected EOF")
        | head :: tail ->
            let state' = parseText state head

            match state' with
            | Ok x -> lex' x tail
            | Error e -> Error e

    lex'
        { Line = 1
          Column = 1
          Tokens = []
          Buffer = [] }
        input


let lexInputFile fileName =
    let input = System.IO.File.ReadAllText(fileName)

    match lex (List.ofSeq input) with
    | Ok x ->
        let tokens = EOF { Line = 0; Column = 0; Value = "" } :: x
        Ok(List.rev tokens)
    | Error e -> Error e
