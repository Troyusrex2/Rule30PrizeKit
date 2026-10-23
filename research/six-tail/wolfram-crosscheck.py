"""Cross-check a finite obstruction with Wolfram's free remote SAT evaluator.

This is exploratory computation, not Wolfram prize verification. It uses no user
account, and sends only the public mathematical model and certificate parameters.
"""
import argparse
import json
from pathlib import Path
import urllib.request

URL = "https://agenttools.wolfram.com/mcp"
HERE = Path(__file__).resolve().parent

CODE = r'''
Clear[check];
check[k_Integer,n_Integer,w_String] := Module[{a,rows,right,clauses,formula,result},
 a=Join[ConstantArray[False,n],Characters[w]/.{"0"->False,"1"->True}];
 rows=Table[Unique["s"],{Length[a]+1},{k}];
 right=Table[Unique["b"],{Length[a]}];
 clauses=Flatten[Table[
   Equivalent[rows[[t+1,j]],
     Xor[If[j==1,a[[t]],rows[[t,j-1]]],
       Or[rows[[t,j]],If[j==k,right[[t]],rows[[t,j+1]]]]]],
   {t,Length[a]},{j,k}]];
 formula=And@@Join[clauses,Not/@Last[rows]];
 result=TimeConstrained[SatisfiableQ[formula],25,"timeout"];
 <|"word"->w,"width"->k,"whiteSteps"->n,"vacuumReachable"->result|>
];
{$Version,check[@@WIDTH@@,@@PADDING@@,"@@WORD@@"]}
'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--width", type=int, required=True)
    parser.add_argument("--padding", type=int, required=True)
    parser.add_argument("--word", required=True)
    args = parser.parse_args()
    assert set(args.word) <= {"0", "1"} and 1 <= args.width <= 20 and 0 <= args.padding <= 100
    headers = {"Content-Type": "application/json", "Accept": "application/json, text/event-stream"}

    def request(payload):
        response = urllib.request.urlopen(urllib.request.Request(URL, json.dumps(payload).encode(), headers), timeout=55)
        return response, response.read().decode()

    response, raw = request({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
        "protocolVersion": "2025-03-26", "capabilities": {}, "clientInfo": {"name": "Rule30Research", "version": "1.0"}}})
    headers["Mcp-Session-Id"] = response.headers["Mcp-Session-Id"]
    headers["MCP-Protocol-Version"] = "2025-03-26"
    request({"jsonrpc": "2.0", "method": "notifications/initialized"})
    code = CODE.replace("@@WIDTH@@", str(args.width)).replace("@@PADDING@@", str(args.padding)).replace("@@WORD@@", args.word)
    _, raw = request({"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {
        "name": "WolframLanguageEvaluator", "arguments": {"code": code, "timeConstraint": 40}}})
    output = HERE / "evidence/wolfram"
    output.mkdir(parents=True, exist_ok=True)
    name = f"{args.word}-K{args.width}-N{args.padding}"
    (output / (name + ".wl")).write_text(code, encoding="utf-8", newline="\n")
    (output / (name + ".json")).write_text(raw, encoding="utf-8", newline="\n")
    print(raw)


if __name__ == "__main__":
    main()
