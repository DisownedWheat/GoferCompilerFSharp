let () =
    match Lexer.lexInputFile "./test_file" with
    | Error e -> printfn "%A" e
    | Ok tokens ->
        // printfn "%A" tokens
        Parser.parse tokens |> printfn "%A"
