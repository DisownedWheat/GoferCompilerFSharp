module Parser

type ParserState =
    { Line: int
      Column: int
      Tokens: Lexer.TokenType list }

type Root = ASTNode list

and GoImport =
    { ModuleName: string
      Alias: string option }

and GoferImport = { ModuleName: string }
and LogicBlock = ASTNode list
and RecordField = Identifier * TypeDeclaration
and RecordDefinition = { Fields: RecordField list }
and RecordLiteral = (Identifier * ASTNode) list

and Identifier =
    { Name: string
      Mutable': bool
      Public': bool }

and TypedIdentifier =
    { Name: string
      Type: TypeDeclaration
      Mutable': bool
      Public': bool }

and IdentifierType =
    | Identifier of Identifier
    | TypedIdentifier of TypedIdentifier
    | ArrayDestructure of Identifier list
    | RecordDestructure of Identifier list
    | TupleDestructure of Identifier list

and TypeDeclaration =
    { Name: string
      Module: string option
      Pointer: bool
      Slice: bool }

and LetDefinition =
    { Left: IdentifierType; Right: ASTNode }

and Assign = { Left: ASTNode; Right: ASTNode }

and ScopedFunctionArg =
    { Name: string
      Type: string
      ScopedName: string }

and FunctionArg =
    | ScopedArg of ScopedFunctionArg
    | TypedArg of TypedIdentifier
    | Arg of Identifier
    | Null

and FunctionDefinition =
    { Name: string
      Args: FunctionArg list
      ReturnType: TypeDeclaration option
      Body: ASTNode
      Struct: (string * ASTNode) option }

and FunctionCall = { Name: string; Args: ASTNode list }

and ASTNode =
    | Root of Root
    | GoImport of GoImport
    | Import of GoferImport
    | FuncDef of FunctionDefinition
    | Let of LetDefinition
    | Block of LogicBlock
    | LetDefinition of LetDefinition
    | AssignExpression of Assign
    | TypeLiteral of TypeDeclaration
    | TypeDefinition of string * ASTNode
    | ParenExpression of ASTNode
    | ArrayLiteral of ASTNode list
    | RecordLiteral of RecordLiteral
    | TupleLiteral of TypeDeclaration list
    | RecordType of RecordDefinition
    | PubDeclaration of ASTNode
    | StringLiteral of string
    | NumberLiteral of string
    | PipeExpression of ASTNode list
    | IdentifierLiteral of IdentifierType
    | ReturnExpression of ASTNode option
    | FunctionCallExpression of FunctionCall
    | NoOp

type ParseDelimiter =
    | FuncDelim of (Lexer.TokenType list -> bool)
    | NoDelimiter

let filterNoOp x =
    match x with
    | NoOp -> false
    | _ -> true

let unexpectedTokenError token =
    match token with
    | Some t ->
        let msg = sprintf "Unexpected token: %A" t
        Error msg
    | None -> Error "Unexpected end of input"

exception ParseException of (Option<Lexer.TokenType> * int * int * string)

let raiseParserError state msg =
    raise (
        ParseException(
            (List.tryHead state.Tokens),
            state.Line,
            state.Column,
            sprintf "Parse error: %s at line %d column %d" msg state.Line state.Column
        )
    )

let updateState (token: Lexer.Token) tokens =
    { Line = token.Line
      Column = token.Column
      Tokens = tokens }

let rec ignoreNewlines tokens =
    match tokens with
    | [] -> []
    | Lexer.NewLine _ :: tail -> ignoreNewlines tail
    | _ -> tokens

[<TailCall>]
let rec parseImport state =
    match state.Tokens with
    | Lexer.String x :: Lexer.NewLine _ :: tail -> (updateState x tail), GoImport { ModuleName = x.Value; Alias = None }
    | Lexer.Identifier x :: Lexer.String y :: Lexer.NewLine tok :: tail ->
        (updateState tok tail),
        GoImport
            { ModuleName = x.Value
              Alias = Some y.Value }
    | Lexer.Identifier x :: Lexer.NewLine tok :: tail -> (updateState tok tail), Import { ModuleName = x.Value }
    | _ -> raiseParserError state "Invalid import statement"

and [<TailCall>] parseParenExpression state =
    let delim =
        FuncDelim(fun x ->
            match x with
            | Lexer.RParen _ :: _ -> true
            | _ -> false)

    parseTree state delim

and [<TailCall>] parseBraceExpression state =
    match ignoreNewlines state.Tokens with
    | Lexer.Identifier _ :: Lexer.Colon _ :: _ -> parseRecord state []
    | _ ->
        let delim =
            FuncDelim(fun x ->
                match x with
                | Lexer.RBrace _ :: _ -> true
                | _ -> false)

        let newState, nodes = recParseTree state delim []
        newState, Block nodes

and [<TailCall>] parseRecord state properties =
    match ignoreNewlines state.Tokens with
    | [] -> state, RecordLiteral properties
    | Lexer.Comma x :: tail -> parseRecord (updateState x tail) properties
    | Lexer.RBrace x :: tail' -> (updateState x tail'), RecordLiteral properties
    | Lexer.Identifier x :: Lexer.Colon y :: tail ->
        let newState, node = matchToken <| updateState y tail

        parseRecord
            newState
            (({ Name = x.Value
                Mutable' = false
                Public' = false },
              node)
             :: properties)
    | _ -> raiseParserError state "Invalid record literal"

and [<TailCall>] parseRecordType state' =
    let checkForComma previousWasComma property =
        match previousWasComma, property with
        | false, Some _ -> true
        | _ -> false

    let rec parse previousWasComma state fields =

        match state.Tokens with
        | [] -> state, List.rev fields
        | Lexer.NewLine x :: remaining -> parse previousWasComma (updateState x remaining) fields
        | Lexer.Comma x :: remaining ->
            if checkForComma previousWasComma (List.tryHead fields) then
                parse true (updateState x remaining) fields
            else
                raiseParserError state "Unexpected comma parsing record type"
        | Lexer.RBrace x :: tail -> ((updateState x tail), (List.rev fields))
        | Lexer.Pub _ :: Lexer.Identifier x :: Lexer.Colon _ :: remaining ->
            let newState, t = parseTypeLiteral <| updateState x remaining

            parse false newState
            <| ({ Name = x.Value
                  Mutable' = false
                  Public' = true },
                t)
               :: fields
        | Lexer.Pub _ :: Lexer.Mut _ :: Lexer.Identifier x :: Lexer.Colon _ :: remaining ->
            let newState, t = parseTypeLiteral <| updateState x remaining

            parse false newState
            <| ({ Name = x.Value
                  Mutable' = true
                  Public' = true },
                t)
               :: fields
        | Lexer.Mut _ :: Lexer.Identifier x :: Lexer.Colon _ :: remaining ->
            let newState, t = parseTypeLiteral <| updateState x remaining

            parse false newState
            <| ({ Name = x.Value
                  Mutable' = true
                  Public' = false },
                t)
               :: fields
        | Lexer.Identifier head :: Lexer.Colon _ :: remaining ->
            let newState, typeDec = parseTypeLiteral <| updateState head remaining

            parse
                false
                newState
                (({ Name = head.Value
                    Mutable' = false
                    Public' = false },
                  typeDec)
                 :: fields)
        | _ ->
            printfn "Tokens: %A\n\n" <| state.Tokens
            raiseParserError state "Invalid record type"

    parse false state' []

and [<TailCall>] parseTupleLiteral state items =
    match state.Tokens with
    | Lexer.RParen x :: tail -> (updateState x tail), TupleLiteral items
    | _ -> raiseParserError state "Not implemented"

and [<TailCall>] parseTypeLiteral state =
    let (isSlice, tail') =
        match state.Tokens with
        | Lexer.LBracket _ :: Lexer.RBracket _ :: tail' -> true, tail'
        | _ -> false, state.Tokens

    let (isPointer, tail'') =
        match tail' with
        | Lexer.Deref _ :: tail'' -> true, tail''
        | _ -> false, tail'

    match tail'' with
    | Lexer.Identifier x :: Lexer.Dot _ :: Lexer.Identifier y :: remaining ->
        ((updateState y remaining),
         { Name = x.Value
           Module = Some(y.Value)
           Pointer = isPointer
           Slice = isSlice })
    | Lexer.Identifier x :: Lexer.Comma _ :: remaining
    | Lexer.Identifier x :: remaining ->
        ((updateState x remaining),
         { Name = x.Value
           Module = None
           Pointer = isPointer
           Slice = isSlice })
    | _ -> raiseParserError state "Invalid type declaration"

and [<TailCall>] parseTypeDec ident state =

    match ignoreNewlines state.Tokens with

    | Lexer.LBrace x :: tail' ->
        let newState, typeDecs = parseRecordType (updateState x tail')
        newState, TypeDefinition(ident, RecordType { Fields = typeDecs })
    | _ ->
        let newState, t = parseTypeLiteral state
        newState, TypeDefinition(ident, TypeLiteral t)

and [<TailCall>] parseArrayLiteral state =
    let delim =
        FuncDelim(fun x ->
            match x with
            | Lexer.RBracket _ :: _ -> true
            | _ -> false)

    let newState, nodes = recParseTree state delim []
    (newState, ArrayLiteral nodes)

and [<TailCall>] parseFunctionArgs state =
    let rec parse' previousWasComma mut state args =
        match (state.Tokens, (previousWasComma || (List.length args) < 1)) with
        | Lexer.RParen x :: tail, _ -> (updateState x tail), args
        | Lexer.Mut x :: tail, true -> parse' previousWasComma true (updateState x tail) args
        | Lexer.Identifier x :: Lexer.Colon _ :: tail, true ->
            let newState, t = parseTypeLiteral <| updateState x tail

            parse' false false newState
            <| TypedArg
                { Name = x.Value
                  Type = t
                  Mutable' = mut
                  Public' = false }
               :: args
        | Lexer.Identifier x :: tail, true ->
            parse' false false (updateState x tail)
            <| Arg
                { Name = x.Value
                  Mutable' = mut
                  Public' = false }
               :: args
        | Lexer.Comma x :: tail, false -> parse' true false (updateState x tail) args
        | _ -> raiseParserError state "Invalid function argument"

    parse' false false state []

and parseStructMethodDefinition state =
    match state.Tokens with
    | Lexer.Identifier x :: tail ->
        let newState, t = parseTypeDec x.Value <| updateState x tail

        let newState' =
            { newState with
                Tokens =
                    match newState.Tokens with
                    | Lexer.RParen _ :: tail -> tail
                    | _ -> raiseParserError newState "Invalid struct method definition" }

        newState', (x.Value, t)
    | _ -> raiseParserError state "Invalid struct method definition"

and [<TailCall>] parseFunction state =
    let matchReturnType state =
        match state.Tokens with
        | Lexer.ReturnType x :: tail ->
            parseTypeLiteral <| updateState x tail
            ||> fun newState returnType -> newState, Some returnType
        | _ -> state, None

    let rec parse' structInfo state =

        match state.Tokens with
        | Lexer.LParen x :: tail ->
            try
                let newState, structInfo = parseStructMethodDefinition <| updateState x tail
                parse' (Some structInfo) newState
            with ParseException _ ->
                match structInfo with
                | Some _ -> raiseParserError state "Invalid struct method definition"

            match newState'.Tokens with
            | Lexer.LBrace x :: tail' ->
                parseBraceExpression <| updateState x tail'
                ||> fun newState' body ->
                    newState',
                    FuncDef
                        { Name = ""
                          Args = List.rev args
                          ReturnType = returnType
                          Body = body }
            | _ -> raiseParserError newState "Invalid function definition"

        | Lexer.Identifier x :: Lexer.LParen _ :: tail ->
            let newState, args = parseFunctionArgs <| updateState x tail
            let newState', returnType = matchReturnType newState

            match newState'.Tokens with
            | Lexer.LBrace brace :: tail' ->
                let newState', body = parseBraceExpression <| updateState brace tail'

                newState',
                FuncDef
                    { Name = x.Value
                      Args = args
                      ReturnType = returnType
                      Body = body
                      Struct = structInfo }
            | _ -> raiseParserError newState "Invalid function definition"

        | _ -> raiseParserError state "Invalid function definition"

    parse' None state

and [<TailCall>] parseLetExpression state =
    let rec parseDestructure delim t' args state' =
        match state'.Tokens with
        | Lexer.Identifier x :: Lexer.Comma c :: remaining ->
            parseDestructure
                delim
                t'
                ({ Name = x.Value
                   Mutable' = false
                   Public' = false }
                 :: args)
                (updateState c remaining)
        | Lexer.Identifier x :: t :: Lexer.Assign a :: remaining when delim t ->
            (updateState a remaining),
            (t' (
                { Name = x.Value
                  Public' = false
                  Mutable' = false }
                :: args
            ))
        | _ -> raiseParserError state "Invalid array destructure"

    let parseArrayDestructure =
        parseDestructure
            (fun x ->
                match x with
                | Lexer.RBracket _ -> true
                | _ -> false)
            ArrayDestructure
            []

    let parseRecordDestructure =
        parseDestructure
            (fun x ->
                match x with
                | Lexer.RBrace _ -> true
                | _ -> false)
            RecordDestructure
            []

    let parseTupleDestructure =
        parseDestructure
            (fun x ->
                match x with
                | Lexer.RParen _ -> true
                | _ -> false)
            TupleDestructure
            []

    let parseLeft state =
        match state.Tokens with
        | Lexer.Identifier x :: Lexer.Colon y :: tail ->
            parseTypeLiteral <| updateState y tail
            ||> fun newState type' ->
                newState,
                TypedIdentifier
                    { Name = x.Value
                      Type = type'
                      Mutable' = false
                      Public' = false }
        | Lexer.Identifier x :: Lexer.Assign y :: tail ->
            updateState y tail,
            Identifier
                { Name = x.Value
                  Mutable' = false
                  Public' = false }
        | Lexer.LParen x :: tail -> parseTupleDestructure <| updateState x tail
        | Lexer.LBrace x :: tail -> parseRecordDestructure <| updateState x tail
        | Lexer.LBracket x :: tail -> parseArrayDestructure <| updateState x tail
        | _ -> raiseParserError state "Invalid left field on assign"

    let newState, left = parseLeft state

    let newState', right =
        matchToken (
            match newState.Tokens with
            | Lexer.Assign x :: tail -> updateState x tail
            | _ -> newState
        )

    newState', LetDefinition { Left = left; Right = right }


and parseFunctionCall (tok: Lexer.Token) state =
    let rec parseArgs state args =
        match state.Tokens with
        | Lexer.RParen x :: tail -> (updateState x tail), args
        | Lexer.Comma x :: tail -> parseArgs (updateState x tail) args
        | _ -> matchToken state ||> fun newState node -> parseArgs newState (node :: args)

    let newState, args = parseArgs state []
    newState, FunctionCallExpression { Name = tok.Value; Args = args }

and parseRecordAccess state = state, NoOp

and parseIndexAccess state = state, NoOp

and parseIdentifier (tok: Lexer.Token) state =
    match state.Tokens with
    | Lexer.LParen x :: tail -> parseFunctionCall tok <| updateState x tail
    | Lexer.Dot x :: tail -> parseRecordAccess <| updateState x tail
    | Lexer.LBracket x :: tail -> parseIndexAccess <| updateState x tail
    | _ ->
        state,
        IdentifierLiteral
        <| Identifier
            { Name = tok.Value
              Mutable' = false
              Public' = false }

and parsePipe node state =
    let rec parse previousWasPipe state' nodes =
        match previousWasPipe, state'.Tokens with
        | false, Lexer.Pipe x :: tail -> parse true (updateState x tail) nodes
        | false, _ -> state', nodes
        | true, _ -> matchToken state' ||> fun newState node -> parse false newState (node :: nodes)

    let newState, nodes = parse false state []
    newState, PipeExpression(node :: (List.rev nodes))

and parseReturn state =
    match state.Tokens with
    | Lexer.NewLine x :: tail -> updateState x tail, ReturnExpression None
    | _ -> matchToken state ||> fun newState node -> newState, ReturnExpression(Some node)

and matchToken state =
    let parse state =
        match state.Tokens with
        | [] -> (state, NoOp)
        | Lexer.Import x :: tail -> parseImport <| updateState x tail
        | Lexer.NewLine x :: tail -> ((updateState x tail), NoOp)
        | Lexer.LBrace x :: tail -> parseBraceExpression <| updateState x tail
        | Lexer.LParen x :: tail -> parseParenExpression <| updateState x tail
        | Lexer.LBracket x :: tail -> parseArrayLiteral <| updateState x tail
        | Lexer.Function x :: tail -> parseFunction <| updateState x tail
        | Lexer.Let x :: tail -> parseLetExpression <| updateState x tail
        | Lexer.Identifier x :: tail -> parseIdentifier x <| updateState x tail
        | Lexer.String x :: tail -> updateState x tail, StringLiteral x.Value
        | Lexer.Number x :: tail -> updateState x tail, NumberLiteral x.Value
        | Lexer.Pub x :: tail -> updateState x tail, NoOp
        | Lexer.Return x :: tail -> parseReturn <| updateState x tail
        | Lexer.TypeKeyword _ :: tail ->
            match ignoreNewlines tail with
            | Lexer.Identifier ident :: Lexer.Assign x :: tail -> parseTypeDec ident.Value <| updateState x tail
            | _ -> raiseParserError state "Invalid type declaration"
        | _ ->
            printfn "%A" <| state.Tokens
            raiseParserError state "Invalid token"

    // Check for pipe operator
    let newState, node = parse state

    match newState.Tokens with
    | Lexer.Pipe x :: tail -> parsePipe node <| updateState x tail
    | Lexer.Assign x :: tail ->
        let newState', right = matchToken <| updateState x tail
        newState', AssignExpression { Left = node; Right = right }

    | _ -> newState, node

and parseTree state delimiter =
    match delimiter, state.Tokens with
    | _, [] -> (state, NoOp)
    | NoDelimiter, _ -> matchToken state
    | FuncDelim f, _ when not (f state.Tokens) -> matchToken state
    | _, _ -> (state, NoOp)

and filterTokensUntilDelimiter delimiter tokens =
    match delimiter, tokens with
    | _, [] -> []
    | NoDelimiter, _ -> ignoreNewlines tokens
    | FuncDelim f, _ ->
        match tokens with
        | [] -> []
        | head :: tail when f [ head ] -> tail
        | head :: tail -> head :: filterTokensUntilDelimiter delimiter tail

and [<TailCall>] recParseTree state delimiter children =
    match delimiter, state.Tokens with
    | _, [] ->
        let filtered = List.filter filterNoOp children |> List.rev

        ({ state with
            Tokens = filterTokensUntilDelimiter delimiter state.Tokens },
         filtered)
    | FuncDelim f, _ when not (f state.Tokens) ->
        let state, child = parseTree state delimiter
        recParseTree state delimiter (child :: children)
    | NoDelimiter, _ ->
        let state, child = parseTree state delimiter
        recParseTree state delimiter (child :: children)
    | _, _ ->
        let filtered = List.filter filterNoOp children |> List.rev

        ({ state with
            Tokens = filterTokensUntilDelimiter delimiter state.Tokens },
         filtered)

and [<TailCall>] recursiveParse state astList =
    match state.Tokens with
    | [] -> [], List.filter filterNoOp astList |> List.rev
    | Lexer.EOF _ :: _ -> [], List.filter filterNoOp astList |> List.rev
    | _ ->
        let newState, child = parseTree state NoDelimiter
        recursiveParse newState (child :: astList)

let parse tokens =
    let _, ast =
        recursiveParse
            { Line = 0
              Column = 0
              Tokens = tokens }
            []

    Root ast
