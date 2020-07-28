let main () =
  let db = Dbm.opendbm "mydb" [Dbm_rdwr] 0o666 in
  Dbm.add db "hello" "world";
  (* ... *)
  Dbm.close db;
  (* ... *)
  print_string (Dbm.find db "hello") (* bug! *)
