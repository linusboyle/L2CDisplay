<TeXmacs|1.99.10>

<style|<tuple|generic|british>>

<\body>
  <doc-data|<doc-title|<name|LDisplay> Source Language
  Syntax>|<doc-author|<author-data|<author-name|Zhilei
  Han>>>|<doc-date|<date>>>

  <section|Preprocessor>

  TODO

  <section|Program>

  \<less\><em|program>\<gtr\> ::= {\<less\><em|decl>\<gtr\>}*

  \<less\><em|decl>\<gtr\> ::=

  \ \ \ \ \| \<less\><em|type_decl>\<gtr\>

  \ \ \ \ \| \<less\><em|const_decl>\<gtr\>

  \ \ \ \ \| \<less\><em|node_decl>\<gtr\>

  \ \ \ \ \| \<less\><em|widget_decl>\<gtr\>

  \ \ \ \ \| \<less\><em|control_decl>\<gtr\>

  <section|Type>

  \<less\><em|type_decl>\<gtr\> ::= <strong|type>
  \<less\><em|type_decl_list>\<gtr\>

  \<less\><em|type_decl_list>\<gtr\> ::= {\<less\><em|one_type_decl>\<gtr\>
  ";"}+

  \<less\><em|one_type_decl>\<gtr\> ::= IDENT "=" \<less\><em|type>\<gtr\>

  \<less\><em|type>\<gtr\> ::=\ 

  \ \ \ \ \| IDENT

  \ \ \ \ \| <strong|bool>

  \ \ \ \ \| <strong|int>

  \ \ \ \ \| <strong|real>

  \ \ \ \ \| <strong|enum> "{" \<less\>id_list\<gtr\> "}"

  \ \ \ \ \| <strong|struct> "{" \<less\>field_list\<gtr\> "}"

  \ \ \ \ \| \<less\><em|type>\<gtr\> "^" INTEGER

  \;

  \<less\><em|field_list>\<gtr\> ::= <em|\<less\>field\<gtr\>> {","
  <em|\<less\>field\<gtr\>>}*

  \<less\><em|field>\<gtr\> ::= IDENT ":" \<less\><em|type>\<gtr\>

  <em|\<less\>id_list\<gtr\>> ::= IDENT {"," IDENT}*

  <section|Const>

  <em|\<less\>const_decl\<gtr\>> ::= <strong|const>
  {<em|\<less\>one_const_decl\<gtr\>> ";"}+

  <em|\<less\>one_const_decl\<gtr\>> ::= IDENT ":" \<less\><em|type>\<gtr\>
  "=" <em|\<less\>const_expr\<gtr\>>

  <em|\<less\>const_expr\<gtr\>> ::=\ 

  \ \ \ \ \| \<less\><em|atom>\<gtr\>

  \ \ \ \ \| \<less\><em|unop>\<gtr\> <em|\<less\>const_expr\<gtr\>>

  \ \ \ \ \| <em|\<less\>const_expr\<gtr\>> <em|\<less\>binop\<gtr\>>
  <em|\<less\>const_expr\<gtr\>>

  \ \ \ \ \| "(" <em|\<less\>const_expr\<gtr\>> ")"

  \ \ \ \ \| "[" <em|\<less\>const_expr\<gtr\>> {","
  <em|\<less\>const_expr\<gtr\>>}* "]"

  \ \ \ \ \| "{" <em|\<less\>field_const_decl\<gtr\>> {","
  <em|\<less\>field_const_decl\<gtr\>>}* "}"

  \<less\><em|atom>\<gtr\> ::=

  \ \ \ \ \| <strong|tru><strong|>e

  \ \ \ \ \| <strong|false>

  \ \ \ \ \| INTEGER

  \ \ \ \ \| REAL

  \ \ \ \ \| IDENT // constant identifier, or an enum constants

  <em|\<less\>field_const_decl\<gtr\>> ::= IDENT ":"
  <em|\<less\>const_expr\<gtr\>>

  <section|Widget Interface>

  <em|\<less\>widget_decl\<gtr\>> ::= <strong|widget> IDENT "("
  \<less\><em|decls>\<gtr\> ")" <strong|returns> "("
  \<less\><em|decls>\<gtr\> ")" ";"

  <section|Control>

  <em|\<less\>control_decl\<gtr\>> ::= <strong|ctrl> IDENT "(" ")"
  <strong|returns> "(" ")" <em|\<less\>control_body\<gtr\>>

  <em|\<less\>control_body\<gtr\>> ::= [var \<less\><em|decls>\<gtr\> ";"]
  <strong|let> \<less\><em|control_equation>\<gtr\>+ <strong|tel> [";"]

  <em|\<less\>control_equation\<gtr\>> ::= <em|\<less\>control_lhs\<gtr\>>
  "=" <em|\<less\>control_rhs\<gtr\>> ";"

  <em|\<less\>control_lhs\<gtr\>> ::= \<less\><em|lhs>\<gtr\> \|
  <em|\<less\>widget_expr\<gtr\>>

  <em|\<less\>control_rhs\<gtr\>> ::= \<less\><em|expr>\<gtr\> \|
  <em|\<less\>widget_expr\<gtr\>>

  <em|\<less\>widget_expr\<gtr\>> ::= MEGA "." IDENT

  <section|Lustre Node>

  <em|\<less\>node_decl\<gtr\>> ::= \<less\><em|funcType>\<gtr\> IDENT "("
  \<less\><em|decls>\<gtr\> ")" <strong|returns> "("
  \<less\><em|decls>\<gtr\> ")" \<less\><em|body>\<gtr\>

  \<less\><em|funcType>\<gtr\> ::= <strong|node> \| <strong|function>

  \<less\><em|decls>\<gtr\> ::= [\<less\><em|var_decl>\<gtr\> {";"
  \<less\><em|var_decl>\<gtr\>}*]

  <em|\<less\>var_decl\<gtr\>> ::= <em|\<less\>id_list\<gtr\>> ":"
  \<less\><em|type>\<gtr\>

  \<less\><em|body>\<gtr\> ::= [var \<less\><em|decls>\<gtr\> ";"]
  <strong|let> \<less\><em|equation>\<gtr\>+ <strong|tel> [";"]

  <em|\<less\>equation\<gtr\>> ::= \<less\><em|lhs>\<gtr\> "="
  \<less\><em|expr>\<gtr\> ";"

  \<less\><em|lhs>\<gtr\> ::= IDENT {"," IDENT}*

  \<less\><em|expr>\<gtr\> ::=

  \ \ \ \ \| \<less\><em|atom>\<gtr\>

  \ \ \ \ \| "(" <em|\<less\>expr_list\<gtr\>> ")"

  \ \ \ \ \| \<less\><em|unop>\<gtr\> \<less\><em|expr>\<gtr\>

  \ \ \ \ \| <strong|pre> \<less\><em|expr>\<gtr\>

  \ \ \ \ \| <strong|current> \<less\><em|expr>\<gtr\>

  \ \ \ \ \| \<less\><em|expr>\<gtr\> <strong|fby> \<less\><em|expr>\<gtr\>

  \ \ \ \ \| \<less\><em|expr>\<gtr\> "-\<gtr\>" \<less\><em|expr>\<gtr\>

  \ \ \ \ \| \<less\><em|expr>\<gtr\> \<less\><em|binop>\<gtr\>
  \<less\><em|expr>\<gtr\>

  \ \ \ \ \| \<less\><em|naryop>\<gtr\> \<less\><em|expr>\<gtr\>

  \ \ \ \ \| <em|\<less\>struct_expr\<gtr\>>

  \ \ \ \ \| <em|\<less\>array_expr\<gtr\>>

  \ \ \ \ \| <em|\<less\>call\<gtr\>>

  \ \ \ \ \| <strong|if> \<less\><em|expr>\<gtr\> <strong|then>
  \<less\><em|expr>\<gtr\> <strong|else> \<less\><em|expr>\<gtr\>

  \;

  \<less\><em|call>\<gtr\> ::= IDENT "(" <em|\<less\>expr_list\<gtr\>> ")"

  <em|\<less\>expr_list\<gtr\>> ::= \<less\><em|expr>\<gtr\> {","
  \<less\><em|expr>\<gtr\>}*

  <em|\<less\>array_expr\<gtr\>> ::=\ 

  \ \ \ \ \| \<less\><em|expr>\<gtr\> \<less\><em|index>\<gtr\>

  \ \ \ \ \| \<less\><em|expr>\<gtr\> "^" INTEGER

  \ \ \ \ \| "[" <em|\<less\>expr_list\<gtr\>> "]"

  \ \ \ \ \| \<less\><em|expr>\<gtr\> "[" \<less\><em|expr>\<gtr\> ".."
  \<less\><em|expr>\<gtr\> "]"

  \;

  \<less\><em|index>\<gtr\> ::= "[" \<less\><em|expr>\<gtr\> "]"

  <em|\<less\>struct_expr\<gtr\>> ::=

  \ \ \ \ \| \<less\><em|expr>\<gtr\> "." IDENT

  \ \ \ \ \| "{" <em|\<less\>field_expr\<gtr\>> {","
  <em|\<less\>field_expr\<gtr\>>}* "}"

  <em|\<less\>field_expr\<gtr\>> ::= IDENT ":" \<less\><em|expr>\<gtr\>

  \;

  \<less\><em|unop>\<gtr\> ::=

  \ \ \ \ \| "+"

  \ \ \ \ \| "-"

  \ \ \ \ \| <strong|not>\ 

  \;

  \<less\><em|binop>\<gtr\> ::=

  \ \ \ \ \| "+"

  \ \ \ \ \| "-"

  \ \ \ \ \| "*"

  \ \ \ \ \| "/"

  \ \ \ \ \| <strong|div>

  \ \ \ \ \| <strong|mod>

  \ \ \ \ \| "\<gtr\>"

  \ \ \ \ \| "\<less\>"

  \ \ \ \ \| "\<gtr\>="

  \ \ \ \ \| "\<less\>-"

  \ \ \ \ \| "\<less\>\<gtr\>"

  \ \ \ \ \| "="

  \ \ \ \ \| <strong|or>

  \ \ \ \ \| <strong|and>

  \ \ \ \ \| <strong|xor>

  \;

  \<less\><em|naryop>\<gtr\> ::=

  \ \ \ \ \| "#"

  \ \ \ \ \| <strong|nor>
</body>

<initial|<\collection>
</collection>>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|?|../../.TeXmacs/texts/scratch/no_name_8.tm>>
    <associate|auto-2|<tuple|2|?|../../.TeXmacs/texts/scratch/no_name_8.tm>>
    <associate|auto-3|<tuple|3|?|../../.TeXmacs/texts/scratch/no_name_8.tm>>
    <associate|auto-4|<tuple|4|?|../../.TeXmacs/texts/scratch/no_name_8.tm>>
    <associate|auto-5|<tuple|5|?|../../.TeXmacs/texts/scratch/no_name_8.tm>>
    <associate|auto-6|<tuple|6|?|../../.TeXmacs/texts/scratch/no_name_8.tm>>
    <associate|auto-7|<tuple|7|?|../../.TeXmacs/texts/scratch/no_name_8.tm>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Preprocessor>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Program>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Type>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Const>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Widget
      Interface> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Control>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|7<space|2spc>Lustre
      Node> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>