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
      mutable': bool
      public': bool }

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
      Body: ASTNode }

and ASTNode =
    | Root of Root
    | GoImport of GoImport
    | Import of GoferImport
    | FuncDef of FunctionDefinition
    | Let of LetDefinition
    | Block of LogicBlock
    | ParenExpression of ASTNode
    | ArrayLiteral of ASTNode list
    | RecordType of RecordDefinition
    | RecordLiteral of RecordLiteral
    | PubDeclaration of ASTNode
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

let raiseParserError state msg token =
    raise (
        ParseException(
            token,
            state.Line,
            state.Column,
            sprintf "Parse error: %s at line %d column %d" msg state.Line state.Column
        )
    )

let updateState (token: Lexer.Token) tokens =
    { Line = token.Line
      Column = token.Column
      Tokens = tokens }

let rec ignoreWhitespace ignoreNewlines tokens =
    match tokens, ignoreNewlines with
    | [], _ -> []
    | Lexer.NewLine _ :: tail, true -> ignoreWhitespace ignoreNewlines tail
    | Lexer.Whitespace _ :: tail, _ -> ignoreWhitespace ignoreNewlines tail
    | _ -> tokens

let rec parseImport state =
    match state.Tokens with
    | Lexer.String x :: Lexer.NewLine _ :: tail -> (updateState x tail), GoImport { ModuleName = x.Value; Alias = None }
    | Lexer.Identifier x :: Lexer.String y :: Lexer.NewLine tok :: tail ->
        (updateState tok tail),
        GoImport
            { ModuleName = x.Value
              Alias = Some y.Value }
    | Lexer.Identifier x :: Lexer.NewLine tok :: tail -> (updateState tok tail), Import { ModuleName = x.Value }
    | _ -> raiseParserError state "Invalid import statement" None

and parseParenExpression state =
    let delim =
        FuncDelim(fun x ->
            match x with
            | Lexer.RParen _ :: _ -> true
            | _ -> false)

    let newState, node = parseTree state delim
    newState, ParenExpression node

and parseBraceExpression state =
    let delim =
        FuncDelim(fun x ->
            match x with
            | Lexer.RBrace _ :: _ -> true
            | _ -> false)

    let newState, nodes = recParseTree state delim []
    newState, Block nodes

and parseRecord state properties =
    match ignoreWhitespace true state.Tokens with
    | [] -> state, RecordLiteral properties
    | Lexer.RBrace x :: tail' -> (updateState x tail'), RecordLiteral properties
    | Lexer.Identifier x :: Lexer.Colon _ :: _ ->
        let newState, node = matchToken state

        parseRecord
            newState
            (({ Name = x.Value
                Mutable' = false
                Public' = false },
              node)
             :: properties)
    | _ -> raiseParserError state "Invalid record literal" (List.tryHead state.Tokens)

and parseRecordType state' =
    let checkForComma previousWasComma property =
        match previousWasComma, property with
        | false, Some _ -> true
        | _ -> false

    let rec parse previousWasComma state fields =
        match ignoreWhitespace true state.Tokens with
        | [] -> state, List.rev fields
        | Lexer.NewLine x :: remaining -> parse previousWasComma (updateState x remaining) fields
        | Lexer.Comma x :: remaining ->
            if checkForComma previousWasComma (List.tryHead fields) then
                parse true (updateState x remaining) fields
            else
                raiseParserError state "Unexpected comma parsing record type" (List.tryHead state.Tokens)
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

            ((updateState head newState.Tokens),
             (({ Name = head.Value
                 Mutable' = false
                 Public' = false },
               typeDec)
              :: fields))
        | _ -> raiseParserError state "Invalid record type" None

    parse false state' []

and parseTypeLiteral state =
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
    | _ -> raiseParserError state "Invalid type declaration" <| List.tryHead tail''

and parseTypeDec state =
    match ignoreWhitespace true state.Tokens with
    | Lexer.LBrace x :: tail' ->
        let newState, typeDecs = parseRecordType (updateState x tail')
        newState, RecordType { Fields = typeDecs }
    | _ -> state, NoOp

and parseArrayLiteral state =
    let delim =
        FuncDelim(fun x ->
            match x with
            | Lexer.RParen _ :: _ -> true
            | _ -> false)

    let newState, nodes = recParseTree state delim []
    (newState, ArrayLiteral nodes)

and matchToken state =
    match state.Tokens with
    | [] -> (state, NoOp)
    | Lexer.Import x :: tail -> parseImport <| updateState x tail
    | Lexer.NewLine x :: tail -> ((updateState x tail), NoOp)
    | Lexer.LBrace x :: tail -> parseBraceExpression <| updateState x tail
    | Lexer.LParen x :: tail -> parseParenExpression <| updateState x tail
    | Lexer.LBracket x :: tail -> parseArrayLiteral <| updateState x tail
    | Lexer.TypeKeyword _ :: tail ->
        match ignoreWhitespace true tail with
        | Lexer.Identifier _ :: Lexer.Assign x :: tail -> parseTypeDec <| updateState x tail
        | _ -> raiseParserError state "Invalid type declaration" <| List.tryHead tail
    | _ -> raiseParserError state "Invalid token" <| List.tryHead state.Tokens

and parseTree state delimiter =
    match delimiter, state.Tokens with
    | _, [] -> (state, NoOp)
    | NoDelimiter, _ -> matchToken state
    | FuncDelim f, _ when not (f state.Tokens) -> matchToken state
    | _, _ -> (state, NoOp)

and recParseTree state delimiter children =
    match delimiter, state.Tokens with
    | _, [] ->
        let filtered = List.filter filterNoOp children |> List.rev
        (state, filtered)
    | FuncDelim f, _ when not (f state.Tokens) ->
        let state, child = parseTree state delimiter
        recParseTree state delimiter (child :: children)
    | NoDelimiter, _ ->
        let state, child = parseTree state delimiter
        recParseTree state delimiter (child :: children)
    | _, _ ->
        let filtered = List.filter filterNoOp children |> List.rev
        (state, filtered)

and recursiveParse state astList =
    match state.Tokens with
    | [] -> [], List.filter filterNoOp astList |> List.rev
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
