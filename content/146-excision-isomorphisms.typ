#import "main-defs.typ": Aut, Im, K, idx, source
#import "statements.typ": proof, theorem
#import "diagrams/exact-k-sequences-squares.typ": (
  category-fiber-square, excision-k-sequence-diagram,
  excision-stabilized-isomorphism, excision-surjectivity-triangle,
  excision-topological-diagram,
)

== Изоморфизмы вырезания <sec:excision-isomorphisms>

#theorem(title: [о вырезании])[
  #idx("теорема о вырезании")Пусть
  $ #category-fiber-square() quad alpha: F_1 G_1 -> F_2 G_2, $
  <eq:excision-cartesian-square>
  ~— декартов квадрат, состоящий из функторов, сохраняющих произведение, причем
  $(F_1, F_2)$ является кофинальной парой (см. @def:cofinal-functor-pair). Пусть
  $ #excision-k-sequence-diagram() $ <eq:excision-k-sequences>
  ~— морфизм точных последовательностей, индуцированный диаграммой. Тогда
  отображение $phi$ сюръективно. Если диаграмма~@eq:excision-cartesian-square
  Е-сюръективна (см. @def:e-surjective-functor-square), например если функтор
  $F_1$ или $F_2$ Е-сюръективен (см. @def:e-surjective-functor), то отображение
  $phi$~— изоморфизм.
] <th:excision-isomorphism>

_Замечание_. Так как предположение о Е-сюръективности диаграммы
@eq:excision-cartesian-square симметрично, то из него вытекает и то, что
отображение $K'_0 (G_1) -> K'_0 (F_2)$ также является изоморфизмом. Как правило,
желая применить эту теорему, мы будем предполагать, что либо #source(305)функтор
$F_1$, либо функтор $F_2$ является Е-сюръективным, и, следовательно, в силу
@prop:fiber-square-cofinality @cond:fiber-square-e-surjectivity диаграмма
@eq:excision-cartesian-square будет Е-сюръективной. Однако предположение о
Е-сюръективности одного из функторов $F_i$ уже не является симметричным.

#proof[
  Отображение $phi$ индуцируется функтором, сохраняющим произведение:
  $ F: italic("co")(G_2) -> italic("co")(F_1), $
  $ F(A, gamma, B) = (G_1 A, alpha_B^(-1)(F_2 gamma)alpha_A, G_1 B). $
  Здесь, конечно, $A = (G_1 A, alpha_A, G_2 A)$,
  $B = (G_1 B, alpha_B, G_2 B) in bold(A)
  = bold(A)_1 times_(bold(A)') bold(A)_2$ и $gamma: G_2 A -> G_2 B$.

  _Отображение $phi$ сюръективно_. Пусть
  $U = (A_1, gamma, B_1) in italic("co")(F_1)$. Поэтому
  $gamma: F_1 A_1 -> F_1 B_1$. Так как функтор $F_2$ кофинален относительно
  функтора $F_1$, то можно найти $A'_1 in bold(A)_1$, $A_2 in bold(A)_2$ и
  изоморфизм $alpha: F_1 (A_1 perp A'_1) -> F_2 A_2$. Определим морфизм $beta$ с
  помощью условия коммутативности диаграммы
  $ #excision-surjectivity-triangle() $
  Тогда $U perp Delta A'_1 = (A_1 perp A'_1, gamma perp 1_(F_1 A'_1),
    B_1 perp A'_1) = F V$, где
  $V = ((A_1 perp A'_1, alpha, A_2), 1_(A_2), (B_1 perp A'_1, beta, A_2))$.
  Таким образом, $[U]' = [U perp Delta A'_1]' = phi[V]'$ в группе $K'_0 (F_1)$.

  _Отображение $phi$ инъективно_. Пусть $phi(x) = 0$. В силу
  @prop:relative-grothendieck-composition-presentation, $x = [U]'$ для
  некоторого объекта $U = (A, gamma, B) in italic("co")(G_2)$. Поэтому
  $[A_1, overline(gamma), B_1]' = 0$ в группе $K'_0 (F_1)$ (где с целью
  сокращения обозначений мы положили $A_i = G_i A$, $B_i = G_i B$ ($i = 1, 2$) и
  $overline(gamma) = alpha_B^(-1)(F_2 gamma)alpha_A$). В частности,
  $[A_1] = [B_1]$ в группе $K_0 (bold(A)_1)$. Поэтому
  $A_1 perp A'_1 tilde.eq B_1 perp A'_1$ для некоторого объекта
  $A'_1 in bold(A)_1$. Так как функтор $G_1$ кофинален (см.
  @prop:fiber-square-cofinality @cond:fiber-square-projection-cofinality), то
  $A'_1 = G_1 A'$ для $A' in bold(A)$. Поскольку
  $x = [U]' = [U perp Delta A']'$, где $Delta A' = (A', 1_(G_2 A'), A')$, то
  можно заменить $U$ на $U perp Delta A'$ и, следовательно, считать, что
  $A_1 tilde.eq B_1$. Используя этот изоморфизм и морфизм $gamma: A_2 -> B_2$,
  можно заменить $B$ на изоморфный объект в $bold(A)$ таким образом, чтобы
  $A_1 = B_1$, $A_2 = B_2$ и $gamma = 1_(A_2)$. Итак, $x = [U]'$, где
  $U = (A, 1_(A_2), B)$, $A = (A_1, alpha_A, A_2)$ и $B = (A_1, alpha_B, A_2)$.
  Если положить $overline(gamma) = alpha_B^(-1)alpha_A$, то
  $B = A overline(gamma)^(-1)$ и поэтому
  $U = (A, 1_(A_2), A overline(gamma)^(-1))$,
  $F U = (A_1, overline(gamma), A_1)$.

  Заметим, что $0 = phi(x) = [A_1, overline(gamma), A_1]'
  = partial' [F_1 A_1, overline(gamma)]$. Следовательно, из рассмотрения точной
  последовательности для функтора $F_1$ следует, что элемент
  $[F_1 A_1, overline(gamma)] in K_1 (bold(A)')$ лежит в
  $Im(K_1 (bold(A)_1) -> K_1 (bold(A)'))$. Так как функтор $F_1 G_1$ кофинален
  #source(306) (см. @prop:fiber-square-cofinality
  @cond:fiber-square-projection-cofinality), то из
  @prop:whitehead-commutator-stabilization вытекает существование
  $A'' in bold(A)$ и $alpha_1 in Aut_(bold(A)_1) (A_1 perp A''_1)$, для которых
  $overline(gamma)^(-1) perp 1_(F_1 A''_1) = (F_1 alpha_1)epsilon$, где
  $epsilon$ принадлежит коммутанту группы
  $Aut_(bold(A)') (F_1 (A_1 perp A''_1))$. Поскольку
  $x = [U]' = [U perp Delta A'']'$, то можно заменить $U$ на $U perp Delta A''$.
  Это не затрагивает ни одной из нормализаций (т. е. равенств $A_1 = B_1$,
  $A_2 = B_2$, $gamma = 1_(A_2)$), достигнутых выше, при этом $overline(gamma)$
  заменяется на $overline(gamma) perp 1_(F_1 A''_1)$. Таким образом, после этой
  замены можно считать, что $overline(gamma)^(-1) = (F_1 alpha_1)epsilon$, и при
  этом все же $U = (A, 1_(A_2), A overline(gamma)^(-1))$.

  В силу нашего предположения диаграмма~@eq:excision-cartesian-square
  Е-сюръективна. Поэтому найдутся объект $C in bold(A)$ и элементы $epsilon_i$
  из коммутанта группы $Aut_(bold(A)_i) (A_i perp C_i)$, для которых морфизм
  $(epsilon_1, epsilon_2): A(F_1 alpha_1)epsilon perp C
  -> A(F_1 alpha_1) perp C$ является изоморфизмом в категории $bold(A)$ (см.
  определение~@def:e-surjective-functor-square). Кроме того,
  $(alpha_1, 1_(A_2)): A(F_1 alpha_1) -> A$ является изоморфизмом в $bold(A)$.
  Из этого получаем изоморфизм в $italic("co")(G_2)$,
  $ #excision-stabilized-isomorphism() $
  Так как элемент $epsilon_2$ лежит в коммутанте группы
  $Aut_(bold(A)_2) (A_2 perp C_2)$, то $[A_2 perp C_2, epsilon_2] = 0$ в группе
  $K_1 (bold(A)_2)$. Таким образом,
  $0 = partial' [G_2 (A perp C), epsilon_2] = [V]'
  = [U perp Delta C]' = [U]' = x$, что и требовалось доказать.
]

Используя изоморфизмы вырезания и последовательность Майера~— Вьеториса для
диаграммы~@eq:excision-cartesian-square, мы получаем хорошо знакомую топологам
естественную процедуру построения коммутативной диаграммы следующего типа:
$ #excision-topological-diagram() $
Средняя линия этой диаграммы представляет собой последовательность Майера~—
Вьеториса, а «синусоидальные кривые» являются $K$-последовательностями для
четырех функторов диаграммы @eq:excision-cartesian-square. Равенства означают
изоморфизмы вырезания.
