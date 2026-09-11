from dataclasses import dataclass
from tree_sitter import Node
from tree_sitter import QueryCursor
from tree_sitter import Query
import argparse
from tree_sitter import Language, Parser
import tree_sitter_ocaml
from textwrap import dedent


def transpose(captures: dict[str, list[Node]]) -> list[dict[str, Node]]:
    ret = []
    for name, cap in captures.items():
        for i, c in enumerate(cap):
            if len(ret) <= i:
                ret.append({})
            ret[i][name] = c
    return ret


@dataclass
class Field:
    app: list[str]


@dataclass
class ConstructorDeclaration:
    name: str
    fields: list[Field]

    @classmethod
    def read(cls, n: Node):
        assert n.type == "constructor_declaration"
        constructor_name = next(
            child for child in n.named_children if child.type == "constructor_name"
        )
        fields = list(
            Field(text(child).split())
            for child in n.named_children
            if child.type != "constructor_name"
        )

        return cls(name=(constructor_name.text or b"").decode(), fields=fields)


def to_string(name: str, cons: list[ConstructorDeclaration]):
    generics = sorted(
        {a.replace("'", "") for c in cons for f in c.fields for a in f.app if "'" in a}
    )
    recursive = any(a == name for c in cons for f in c.fields for a in f.app)

    def mk_name(name: str):
        return f"{name}_to_string"

    def field_des(f: list[Field]) -> str:
        if len(f) == 0:
            return ""
        ret = ", ".join(f"i{i}" for i, _ in enumerate(f))
        if len(f) == 1:
            return ret
        return f"({ret})"

    def call(app: list[str], v: str):
        return " ".join(mk_name(i.replace("'", "")) for i in app[::-1]) + " " + v

    def field_str(fields: list[Field]) -> str:
        if len(fields) == 0:
            return ""
        x = [f"({call(f.app, f'i{i}')})" for i, f in enumerate(fields)]
        ret = ' ++ ", " ++ '.join(x)
        if len(fields) == 1:
            return '++ " " ++ ' + ret
        return f'++ " (" ++ {ret} ++ ")"'

    cases = [
        f'| {c.name} {field_des(c.fields)} -> "{c.name}" {field_str(c.fields)} '
        for c in cons
    ]
    rec = "rec " if recursive else ""
    return dedent(f"""\
    let {rec}{mk_name(name)} {" ".join(mk_name(g) for g in generics)} x = match x with
    {"\n    ".join(cases)}
    """)


def text(n: Node) -> str:
    return (n.text or b"").decode()


def sum_type(name: str, decl: Node):
    cases = decl.named_children
    cons = [ConstructorDeclaration.read(n) for n in cases]
    # for c in cons:
    #     print(f"  {c.name} {c.fields}")
    print(to_string(name, cons))
    # print([(i.type, i.text) for i in decl.named_children])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("file")
    args = parser.parse_args()
    language_ocaml = Language(tree_sitter_ocaml.language_ocaml())

    parser = Parser(language_ocaml)
    with open(args.file, "rb") as f:
        tree = parser.parse(f.read())

    q = Query(
        language_ocaml,
        """
    (type_definition
    (type_binding
      name: (_) @name
      body: (_) @body))
    """,
    )
    qc = QueryCursor(q)
    captures = qc.captures(tree.root_node)

    for i, x in qc.matches(tree.root_node):
        name = x["name"][0]
        body = x["body"][0]

        assert body.type == "variant_declaration"
        sum_type(text(name), body)

    # for c in transpose(captures):
    #     assert c["body"].type == "variant_declaration"
    #     sum_type((c["name"].text or b"").decode(), c["body"])
    # print(c["name"].text)
    # print([(i.type, i.text) for i in c["body"].named_children])
    # print(c["body"])


if __name__ == "__main__":
    main()
