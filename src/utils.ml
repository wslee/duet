open Cil
open Pretty
open Profiler
open Vocab

let save_bin cil fname =
  let fname = Filename.basename fname in
  let oc = open_out (!Options.outdir ^ "/" ^ fname) in
  Marshal.to_channel oc cil [];
  close_out oc

let load_bin fname =
  let fname = Filename.basename fname in
  let ic = open_in (!Options.outdir ^ "/" ^ fname) in
  let cil = Marshal.from_channel ic in
  close_in ic;
  cil

class simpleCilPrinterClass = object (self)
  inherit Cil.defaultCilPrinterClass as super
  method pLineDirective ?(forcefile=false) l = Pretty.nil
  method pGlobal () global =
    match global with
    | Cil.GVarDecl (vi, l) when Hashtbl.mem Cil.builtinFunctions vi.vname ->
      Pretty.nil
    | Cil.GVarDecl (vi, l) ->
      (match vi.vtype with
       | TFun (_, _, _, attr) ->
          if List.mem (Cil.Attr ("missingproto", [])) attr then Pretty.nil
          else (super#pVDecl () vi) ++ text ";\n"
       | _ -> (super#pVDecl () vi) ++ text ";\n")
    | _ -> super#pGlobal () global
end

let dumpFile pp out file =
  Pretty.fastMode := true;
  Cil.iterGlobals file (fun g -> Cil.dumpGlobal pp out g);
  flush out

let save cil fname =
  (try Unix.unlink fname with _ -> ());
  let oc = open_out fname in
  dumpFile (new simpleCilPrinterClass) oc cil;
  close_out oc

let tmp_counter = ref (-1)
let save_temp cil fname success =
  tmp_counter := !tmp_counter + 1;
  if !Options.save_temp then
    let fname =
      !Options.outdir ^ "/" ^ Filename.basename fname ^ "."
      ^ string_of_int !tmp_counter ^ "."
      ^ (if success then "success.c" else "fail.c")
    in
    let oc = open_out fname in
    dumpFile (new simpleCilPrinterClass) oc cil;
    close_out oc
  else ()

let check cil =
  Profiler.check_start ();
  save cil !Frontend.fname;
  let _ = Unix.create_process !Frontend.oracle [|!Frontend.oracle|] Unix.stdin Unix.stdout Unix.stderr in
  let r = match snd (Unix.wait ()) with
    | Unix.WEXITED 0 -> true
    | _ -> false
  in
  Profiler.check_end ();
  r

let wordcount cil =
  save cil !Frontend.fname;
  let (fd_in, fd_out) = Unix.pipe () in
  let _ = Unix.create_process "wc" [|"wc"; "-w"; !Frontend.fname|] Unix.stdin fd_out Unix.stderr in
  match snd (Unix.wait ()) with
  | Unix.WEXITED 0 ->
    (try
       Unix.in_channel_of_descr fd_in |> input_line |> String.split_on_char ' '
       |> flip List.nth 0 |> int_of_string
     with _ -> -1)
  | _ -> -1

let prdbg_endline s =
  if !Options.debug then prerr_endline s
  else ()
