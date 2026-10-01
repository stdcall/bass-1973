#import "main-defs.typ": (
  Coim, Coker, Ex, H, Im, K, Ker, idx, mor, name-idx, ob, source, symbol-idx,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, example, item-record, lemma, proof,
  theorem,
)
#import "diagrams/abelian-k-theory-localization.typ": (
  localization-common-representation, localization-complex-lift,
  localization-composition, localization-exact-comparison,
  localization-exact-functor-square, localization-k0-triangle,
  localization-monic-representation, localization-refinement,
)

== Точная последовательность для функтора локализации <sec:quotient-categories>

Пусть $overline(S):bold(A) -> bold(B)$ — точный функтор, причем категории
$bold(A)$ и $bold(B)$ абелевы. Через
$ bold(S)="«"Ker overline(S)"»" $
обозначим полную подкатегорию объектов $A in bold(A)$, для которых
$overline(S) A=0$. Так как функтор $overline(S)$ точный, то очевидно, что Если
последовательность $0 -> A' -> A -> A'' -> 0$ точна в категории $bold(A)$, то
$ A in bold(S) <=> A',A'' in bold(S). $ <eq:serre-subcategory-closure>
В общем случае будем называть полную подкатегорию $bold(S) subset bold(A)$
_подкатегорией Серра_,#idx("подкатегория Серра") если она удовлетворяет условию
@eq:serre-subcategory-closure. Приведенный выше метод построения подкатегорий
Серра (как «ядер» точных функторов) фактически является единственным:

#theorem[
  Пусть $bold(S)$ — подкатегория Серра абелевой категории $bold(A)$. Тогда
  существуют абелева категория $bold(A) slash bold(S)$ и точный #source(
    328,
  )функтор «факторизации» $overline(S):bold(A) -> bold(A) slash bold(S)$, для
  которого $bold(S)="«"Ker overline(S)"»"$, являющийся решением следующей
  универсальной задачи: для любого точного функтора $T:bold(A) -> bold(B)$,
  такого, что $T A=0$ для всех $A in bold(S)$, существует и при этом
  единственный функтор $U:bold(A) slash bold(S) -> bold(B)$, для которого
  $T=U compose overline(S)$. Кроме того, функтор $U$ точный.
] <th:serre-quotient-category>

Мы не будем доказывать здесь эту теорему. Вместо этого отошлем читателя к статье
Габриеля#name-idx("Габриель (Gabriel P.)") @bib:Gabriel1962, гл. III. Наша цель
— получить ряд свойств функтора факторизации $overline(S)$ из этой теоремы (при
этом фактически достаточно указать, как строить категорию
$bold(A) slash bold(S)$) и использовать их для доказательства теоремы
Хеллера#idx("теорема Хеллера") @th:heller-localization-k0, утверждающей, что
$ K'_0 (overline(S)) tilde.eq K_0 (bold(S)). $
Этот изоморфизм чрезвычайно полезен и позволяет нам во многих интересных случаях
вычислить группу $K'_0 (overline(S))$.

Поскольку читатель обременен рядом недоказанных предложений, мы приведем два
основных примера ситуации, описанной в теореме @th:serre-quotient-category,
которые полезно иметь в виду. На этих примерах следующие далее предложения могут
быть проверены непосредственно. Они также поясняют, как конструкция
факторкатегории связана с «локализацией».

#example[
  Пусть $S$ — мультипликативная система коммутативного кольца $R$, пусть $A$
  является $R$-алгеброй и $bold(S) subset italic("mod")-A$ — подкатегория Серра
  модулей $M$, в которых для каждого $x in M$ найдется элемент $s in S$, такой,
  что $x s=0$. Пусть
  $overline(S):italic("mod")-A -> (italic("mod")-A) slash bold(S)$ — функтор
  факторизации. Так как функтор локализации
  $S^(-1):italic("mod")-A -> italic("mod")-(S^(-1) A)$ аннулирует $bold(S)$, то
  существует функтор
  $U:(italic("mod")-A) slash bold(S) -> italic("mod")-(S^(-1) A)$, для которого
  $S^(-1)=U compose overline(S)$. Важно отметить, что $U$ — эквивалентность и,
  следовательно, функтор локализации $S^(-1)$ является функтором факторизации.
] <exm:module-serre-localization>

#example[
  Пусть $A$ — пучок колец на топологическом пространстве $X$. Через
  $italic("mod")-A$ обозначим категорию пучков $A$-модулей. Пусть $U$ — открытое
  множество, $F$ — его дополнение. Рассмотрим функтор ограничения
  $overline(S):italic("mod")-A -> italic("mod")-(A|_U)$. Тогда, как и в
  предыдущем примере, функтор $overline(S)$ эквивалентен функтору факторизации,
  объектами «ядра» которого служат пучки $A$ с носителями в $F$.
] <exm:sheaf-serre-localization>

_Зафиксируем до конца параграфа функтор факторизации_
$ overline(S):bold(A) -> bold(A)'=bold(A) slash bold(S). $
Через $I$ обозначим множество морфизмов $f$ категории $bold(A)$, для которых
$overline(S) f$ — изоморфизм. Если $A,B in bold(A)$ и
$overline(f):overline(S) A -> overline(S) B$ — #source(329)морфизм категории
$bold(A)'$, то будем говорить, что диаграмма
$ A arrow.l^a A' arrow.r^f B' arrow.l^b B $
в категории $bold(A)$ является _представлением_ морфизма $overline(f)$ #idx(
  "представление морфизма",
) или что она _представляет_ $overline(f)$, #idx(
  "представляет (морфизм, о диаграмме)",
) если $a,b in I$ и
$overline(f)=(overline(S) b)^(-1)(overline(S) f)(overline(S) a)^(-1)$. Два
других утверждения о функторе $overline(S)$ дополняют теорему
#[@th:serre-quotient-category]:
#condition-list[
  #condition-item[функтор $overline(S)$ биективен на объектах;]
  <cond:localization-bijective-objects>

  #condition-item[каждый морфизм в категории $bold(A)'$ обладает
    представлением.]
  <cond:localization-morphism-representations>

  Выведем теперь ряд других свойств.

  #condition-item[Пусть диаграмма $A arrow.l^a A' arrow.r^f B' arrow.l^b B$
    представляет морфизм $overline(f)$. Тогда можно построить коммутативную
    диаграмму
    $ #localization-refinement() $
    где верхний прямоугольник является «кодекартовым квадратом», а нижний —
    декартовым квадратом. Так как $a,b in I$, то легко показать, что
    $a',b' in I$. Например, поскольку функтор $overline(S)$ точный, то он
    сохраняет декартовы и кодекартовы квадраты, и поэтому утверждение следует из
    того, что декартов или кодекартов квадрат изоморфизма является снова
    изоморфизмом. Следовательно, мы получили новые представления
    $ A arrow.r^(f_A) B'' arrow.l^(b' b) B $
    и
    $ A arrow.l^(a a') A'' arrow.r^(f_B) B=B $
    морфизма $overline(f)$.] <cond:localization-refined-representations>

  #condition-item[Предположим, что
    $overline(S) A arrow.r^(overline(f)) overline(S) B
    arrow.r^(overline(g)) overline(S) C$ — два морфизма из категории $bold(A)'$
    соответственно с представлениями $A arrow.l^a A' arrow.r^f B' arrow.l^b B$ и
    $B arrow.l^(b_1) B_1 arrow.r^g C' arrow.l^c C$. Тогда построим диаграмму
    (как в @cond:localization-refined-representations)
    $ #localization-composition() $
    #source(330)Заметим, что
    $A arrow.l^(a a') A'' arrow.r^(g_B f_B) C'' arrow.l^(c' c) C$
    является представлением морфизма $overline(g) overline(f)$.]
  <cond:localization-composite-representation>

  #condition-item[Если $A arrow.l^(a_i) A'_i arrow.r^(f_i) B'_i arrow.l^(b_i) B$
    ($i=0,1$) — два представления морфизма $overline(f)$, то существует
    коммутативная диаграмма
    $ #localization-common-representation() $
    средняя строка которой также представляет морфизм $overline(f)$. При этом
    $alpha_i,beta_i in I$ ($i=0,1$). Чтобы в этом убедиться, рассмотрим объекты
    с буквой $A$ как углы декартова квадрата, а объекты с буквой $B$ как углы
    кодекартова квадрата. Полагая $f'_i=beta_i f_i alpha_i$ ($i=0,1$), видим,
    что $overline(S) f'_0=overline(S) f'_1$, поэтому и
    $Im (f'_1-f'_0) in bold(S)$. Следовательно, если мы заменим $B'$ на
    $Coker (f'_1-f'_0)$, то можно соответственно сплющить диаграмму справа так,
    что вся диаграмма будет коммутативна, причем $f$ индуцируется с помощью
    $f'_0$ (и $f'_1$).]
  <cond:localization-common-representation>

  #condition-item[Пусть диаграмма $A arrow.l^a A' arrow.r^f B' arrow.l^b B$
    представляет морфизм $overline(f)$. Тогда можно построить коммутативную
    диаграмму:
    $ #localization-monic-representation() $
    начиная с левой вершины и двигаясь вправо и вниз. Нижняя часть диаграммы
    задает тогда новое представление морфизма $overline(f)$, для которого $a_2$
    — мономорфизм, а $b_2$ — эпиморфизм.]
  <cond:localization-monic-epic-representation>

  #condition-item[Пусть диаграмма в категории $bold(A)'$
    $ #localization-complex-lift(quotient: true) $
    #source(331)коммутативна. Тогда в категории $bold(A)$ найдется следующая
    коммутативная диаграмма:
    $ #localization-complex-lift() $
    В ней вертикали задают представления морфизмов $gamma_2,gamma_1$ и $gamma_0$
    соответственно, все $a_i$ — мономорфизмы, а все $b_i$ — эпиморфизмы. В
    частности, если морфизмы $alpha_0 alpha_1$ и $beta_0 beta_1$ нулевые,
    нулевыми являются и морфизмы $alpha'_0 alpha'_1$ и $beta'_0 beta'_1$.

    Построение такой диаграммы начнем с вертикальных представлений для
    $gamma_i$. Поэтому, используя установленное свойство
    @cond:localization-monic-epic-representation, мы считаем, что все $a_i$ —
    мономорфизмы и все $b_i$ — эпиморфизмы. Для завершения построения произведем
    замену $A'_i$ и $B'_i$ на «более малые» объекты. Для $A'_i$ это означает
    выбор более малого подобъекта в $A_i$, для которого вложение в $A_i$ все еще
    принадлежит множеству $I$. Для $B'_i$ это означает выбор более малого
    факторобъекта объекта $B_i$, для которого проекция из $B_i$ на него все еще
    принадлежит $I$.

    _Шаг 1._ Выберем $A'_1$ и $B'_1$ такими малыми, чтобы существовали
    $alpha'_0$ и $beta'_1$, превращающие верхний правый и нижний левый
    прямоугольники соответственно в коммутативные диаграммы.

    _Шаг 2._ Выберем $A'_2$ и $B'_0$ такими малыми, чтобы существовали
    $alpha'_1$ и $beta'_0$, для которых верхний левый и нижний правый
    прямоугольники будут коммутативными.

    _Шаг 3._ Выберем $B'_0$ еще меньшим, так, чтобы средний правый прямоугольник
    был коммутативным.

    _Шаг 4._ Выберем $B'_1$ настолько малым, чтобы средний левый прямоугольник
    был коммутативным.

    Легко заметить, что все эти редукции осуществимы, при этом каждый из
    следующих шагов сохраняет достигнутое на предыдущих шагах.]
  <cond:localization-complex-representation>

  #condition-item[Если $overline(A)=(0 -> overline(A)_2 -> overline(A)_1
      arrow.r^(overline(f)) overline(A)_0 -> 0) in Ex (bold(A)')$, т. е.
    $overline(A)$ — короткая точная последовательность в категории $bold(A)'$,
    то существуют $A in Ex (bold(A))$ и изоморфизм
    $overline(S) A tilde.eq overline(A)$. Действительно, так как функтор
    $overline(S)$ точный, то достаточно поднять морфизм $overline(f)$ до
    эпиморфизма $f:A_1 -> A_0$ в категории $bold(A)$. #source(332)Положим
    $overline(A)_i=overline(S) B_i$. Используя
    @cond:localization-refined-representations, можно представить морфизм
    $overline(f)$ диаграммой $B_1=B_1 arrow.r^(f') B'_0 arrow.l^(b_0) B_0$.
    Пусть теперь $A_1=B_1$ и $A_0=Im (f') -> B'_0$ — вложение. Тогда отображение
    $
      (1_(overline(S) B_1),(overline(S) b_0)^(-1)(overline(S) i)):
      (overline(S) A_1 arrow.r^(overline(S) f) overline(S) A_0)
      -> (overline(S) B_1 arrow.r^(overline(f)) overline(S) B_0)
    $
    является требуемым изоморфизмом.]
  <cond:localization-exact-sequence-lift>
]

#theorem(title: [Хеллер])[
  #idx("теорема Хеллера")
  Пусть $overline(S):bold(A) -> bold(A)'=bold(A) slash bold(S)$ — функтор
  факторизации, $bold(C)$ — такая допустимая подкатегория категории $bold(A)$,
  что из $A in bold(A)$, $C in bold(C)$ и $overline(S) A tilde.eq overline(S) C$
  следует, что $A in bold(C)$. Пусть $bold(C)'$ — полная подкатегория категории
  $bold(A)'$ с объектами $overline(S) A$ ($A in bold(C)$) и
  $S:bold(C) -> bold(C)'$ — функтор, индуцированный функтором $overline(S)$.
  Тогда функтор $F:bold(S) -> italic("co")(S)$, для которого $F(A)=(0,0,A)$,
  индуцирует изоморфизм $phi:K_0 (bold(S)) -> K'_0 (S)$.
] <th:heller-localization-k0>

*Замечание.* Условие @cond:admissible-kernel-closure в определении
@def:admissible-abelian-subcategory допустимой подкатегории не является здесь
необходимым и не используется в доказательстве.

#proof[
  Заметим сначала, что функтор $F$ точный и, следовательно, существует
  гомоморфизм $phi$. Пусть $(A,alpha,B) in italic("co")(S)$ и диаграмма
  $A arrow.l^a A' arrow.r^f B' arrow.l^b B$ представляет морфизм $alpha$. Из
  предположений о категории $bold(C)$ следует, что $A',B' in bold(C)$. Таким
  образом, из равенства $alpha=(S b)^(-1)(S f)(S a)^(-1)$ вытекает, что
  $ [A,alpha,B]=[A',S f,B']-[A',S a,A]-[B,S b,B'] $
  в группе $K'_0 (S)$. Кроме того, можно рассмотреть фильтрацию для
  $(A',S f,B')$ в $italic("co")(S)$:
  $ (Ker f,0,0) subset (A',overline(f),Im (f)) subset (A',S f,B'), $
  где морфизм $overline(f):S A' -> S Im (f)=Im (S f)$ индуцирован отображением
  $S f$. Так как последовательные факторы лежат в $italic("co")(S)$, то
  $ [A',S f,B']=[Ker f,0,0]+[Coim f,S g,Im f]+[0,0,Coker f]. $
  Здесь $g$ является изоморфизмом, индуцированным отображением $f$. Поэтому мы
  получаем изоморфизм
  $ (g,1):(Coim f,S g,Im f) -> (Im f,1,Im f). $
  Из этого следует, что $[Coim f,S g,Im f]=0$. Далее заметим, что если
  $C in bold(S)$, то
  $ (C,0,0) plus.o (0,0,C)=(C,0,C) subset (C,1_(S C),C) $
  #source(333)и, следовательно, $[C,0,0]=-[0,0,C]$. Таким образом,
  $[A',S f,B']=[0,0,Coker f]-[0,0,Ker f]
  =phi([Coker f]-[Ker f])$. Аналогичное заключение можно сделать для
  $(A',S a,A)$ и $(B,S b,B')$.

  Если морфизм $f$ лежит в $I$, то положим
  $ chi(f)=[Coker f]-[Ker f] in K_0 (bold(S)). $
  Итог предыдущих рассуждений: если $(A,alpha,B) in italic("co")(S)$ и диаграмма
  $A arrow.l^a A' arrow.r^f B' arrow.l^b B$ представляет морфизм $alpha$, то
  $ [A,alpha,B]=phi(chi(f)-chi(a)-chi(b)). $
  Это подсказывает такое определение отображения
  $ psi:ob italic("co")(S) -> K_0 (bold(S)) $
  с помощью $psi(A, alpha, B)=chi(f)-chi(a)-chi(b)$. Если мы покажем, что
  отображение $psi$ определено корректно и индуцирует гомоморфизм
  $psi:K'_0 (S) -> K_0 (bold(S))$, то из приведенного выше равенства будет
  вытекать, что $phi compose psi$ является тождественным отображением. С другой
  стороны, если $A in bold(S)$, то можно представить морфизм
  $0 in bold(A)'(S 0,S A)$ диаграммой $0=0 arrow.r^f A=A$. Поэтому
  $psi(phi[A])=psi[0,0,A]=[Coker f]-[Ker f]=[A]$. Следовательно, теорема будет
  доказана, как только мы покажем, что:
  #condition-list[
    #condition-item[отображение $psi$ определено корректно;]
    <cond:localization-psi-well-defined>

    #condition-item[если $(A,alpha,B),(B,beta,C) in italic("co")(S)$, то
      $psi(A, beta alpha, C)=psi(A, alpha, B)+psi(B, beta, C)$;]
    <cond:localization-psi-composition>

    #condition-item[если последовательность
      $0 -> (A_2,gamma_2,B_2) -> (A_1,gamma_1,B_1) -> (A_0,gamma_0,B_0) -> 0$
      точна в $italic("co")(S)$, то
      $psi(A_1, gamma_1, B_1)=psi(A_2, gamma_2, B_2)+psi(A_0, gamma_0, B_0)$.]
    <cond:localization-psi-additivity>
  ]

  Заметим сначала, что если $f,g in I$ и произведение $g f$ определено, то
  $chi(g f)=chi(g)+chi(f)$. Это следует из точности последовательности
  #[@prop:composite-kernel-cokernel]:
  $
    0 -> Ker f -> Ker (g f) -> Ker g -> Coker f -> Coker (g f) -> Coker g -> 0.
  $

  _Доказательство #[@cond:localization-psi-well-defined]._
  Если две диаграммы $A arrow.l^(a_i) A'_i arrow.r^(f_i) B'_i arrow.l^(b_i) B$
  ($i=0,1$) представляют морфизм $alpha$, где $(A,alpha,B) in italic("co")(S)$,
  то мы построим, как и в @cond:localization-common-representation,
  коммутативную диаграмму. Тогда
  $
    chi(f')-chi(a)-chi(b)=chi(beta_i f_i alpha_i)-chi(a_i alpha_i)
    -chi(beta_i b_i)=chi(f_i)-chi(a_i)-chi(b_i) quad "для" quad i=0,1.
  $

  _Доказательство #[@cond:localization-psi-composition]._
  Используя @cond:localization-refined-representations, можно выбрать такие
  представления $A arrow.l^a A' arrow.r^f B=B$ морфизма $alpha$ и
  $B=B arrow.r^g C' arrow.l^c C$ #source(334)морфизма $beta$, что диаграмма
  $A arrow.l^a A' arrow.r^(g f) C' arrow.l^c C$ представляет морфизм
  $beta alpha$. Следовательно,
  $
    psi(A, beta alpha, C)=chi(g f)-chi(a)-chi(c)
    =(chi(f)-chi(a))+(chi(g)-chi(c))=psi(A, alpha, B)+psi(B, beta, C).
  $

  _Доказательство #[@cond:localization-psi-additivity]._
  Начиная с данной точной последовательности в категории $italic("co")(S)$,
  построим, как и в @cond:localization-complex-representation, коммутативную
  диаграмму. Будем рассматривать строки как комплексы (нулевые объекты всюду,
  кроме степеней $0,1,2$), а вертикали как морфизмы комплексов:
  $A arrow.l^a A' arrow.r^f B' arrow.l^b B$. Здесь, например,
  $A=(dots A_2 -> A_1 -> A_0 dots)$, $a=(dots,a_2,a_1,a_0,dots)$ и т. д.
  Рассмотрим некоторые точные последовательности комплексов:
  $ 0 -> A' arrow.r^a A -> Coker (a) -> 0, $
  $ 0 -> Ker (f) -> A' -> Im (f) -> 0, $
  $ 0 -> Im (f) -> B' -> Coker (f) -> 0, $
  $ 0 -> Ker (b) -> B -> B' -> 0. $
  Так как $S f,S a$ и $S b$ — изоморфизмы, то ядра и коядра отображений $f,a$ и
  $b$ являются комплексами в $bold(S)$. Кроме того, поскольку комплексы $A$ и
  $B$ ацикличны, комплексы $S A'$ и $S B'$ также ацикличны. Поэтому $H A'$ и
  $H B'$ являются градуированными объектами в категории $bold(S)$.

  Если $C=(C_n)$ — конечный градуированный объект в категории $bold(S)$, то
  положим $chi^bold(S)(C)=sum_n (-1)^n [C_n] in K_0 (bold(S))$. Используя это
  обозначение, можно переформулировать утверждение
  #[@cond:localization-psi-additivity]:
  $
    chi^bold(S)(Coker (f))-chi^bold(S)(Ker (f))
    =chi^bold(S)(Coker (a))-chi^bold(S)(Ker (b)).
  $
  <eq:localization-euler-identity>
  Для его доказательства напомним сначала (см.
  @prop:euler-characteristic-identities @cond:euler-homology-invariance), что
  если $C$ — конечный комплекс в $bold(S)$, то
  $chi^bold(S)(H(C))=chi^bold(S)(C)$, и (см.
  @prop:euler-characteristic-identities @cond:euler-exact-complex-homology), что
  если последовательность комплексов $0 -> C' -> C -> C'' -> 0$ с конечным
  числом ненулевых групп гомологии из $bold(S)$ точна, то
  $chi^bold(S)(H(C))=chi^bold(S)(H(C'))+chi^bold(S)(H(C''))$. Принимая во
  внимание этот факт и точность выписанных последовательностей, видим, что
  $ 0=chi^bold(S)(H A')+chi^bold(S)(Coker (a)), $
  $ chi^bold(S)(H A')=chi^bold(S)(Ker (f))+chi^bold(S)(H Im (f)), $
  $ chi^bold(S)(H B')=chi^bold(S)(H Im (f))+chi^bold(S)(Coker (f)), $
  $ 0=chi^bold(S)(Ker (b))+chi^bold(S)(H B'). $
  Вычитая второе равенство из третьего, получаем, что
  $chi^bold(S)(Coker (f))-chi^bold(S)(Ker (f))
  =chi^bold(S)(H B')-chi^bold(S)(H A')$. Вычитая из него первое #source(335)и
  последнее равенства, получим @eq:localization-euler-identity. Это завершает
  доказательство теоремы @th:heller-localization-k0.
]

#corollary[
  Сохраним обозначения теоремы @th:heller-localization-k0. Тогда функторы
  $bold(S) subset bold(C) arrow.r^S bold(C)'$ индуцируют точную
  последовательность
  $ K_0 (bold(S)) arrow.r^d K_0 (bold(C)) -> K_0 (bold(C)') -> 0. $
  Кроме того, существует «связывающий гомоморфизм»
  $partial:K_1 (bold(C)') -> K_0 (bold(S))$, определенный так: если
  $(S A,alpha) in Sigma bold(C)'$ и диаграмма
  $A arrow.l^a A' arrow.r^f B' arrow.l^b A$ представляет морфизм $alpha$, то
  $partial[S A,alpha]_(bold(C)')=chi(f)-chi(a)-chi(b)$. Здесь для
  $g in mor bold(C)$, такого, что $S g$ — изоморфизм, мы определили
  $chi(g)=[Coker g]-[Ker g]$. Последовательность
] <cor:localization-k-sequence>

#item-record[$
  K_1 (bold(C)) -> K_1 (bold(C)') arrow.r^partial K_0 (bold(S))
  arrow.r^d K_0 (bold(C)) -> K_0 (bold(C)') -> 0
$] <ss:localization-k-exact-sequence>

_точна всюду, кроме, возможно, члена $K_1 (bold(C)')$, если категория $bold(C)'$
полупроста, и точна, если категория $bold(C)$ полупроста._

#proof[
  В силу @cond:localization-exact-sequence-lift если $A' in Ex (bold(C)')$ (т.
  е. $A'$ — короткая точная последовательность в категории $bold(C)'$), то
  найдется объект $A in Ex (bold(A))$, для которого $overline(S) A tilde.eq A'$.
  Тогда автоматически $A in Ex (bold(C))$, и поэтому отображение
  $Ex (S):Ex (bold(C)) -> Ex (bold(C)')$ сюръективно на классах изоморфных
  объектов. Таким образом, предложение @prop:cofinal-exact-boundary-descent
  приводит нас к последовательности
  $
    dots K_1 (bold(C)) -> K_1 (bold(C)') arrow.r^(partial') K'_0 (S)
    arrow.r^(d') K_0 (bold(C)) -> K_0 (bold(C)') -> 0,
  $
  которая точна, если отбросить два левых члена. Более того, она точна и в этих
  членах, что обеспечивается соответствующими предположениями о полупростоте в
  теореме @th:semisimple-exact-k-sequence. Только что доказанная теорема
  @th:heller-localization-k0 дает изоморфизм $phi:K_0 (bold(S)) -> K'_0 (S)$,
  позволяющий заменить $K_0 (bold(S))$ на $K'_0 (S)$ в этой последовательности.
  Если $A in bold(S)$, то $d' phi[A]_(bold(S))=d'[0,0,A]_S=-[A]_(bold(C))$, и
  поэтому отображение $d=-d' phi$ индуцируется вложением
  $bold(S) subset bold(C)$. Кроме того, определение отображения $psi$
  ($=phi^(-1)$) в доказательстве теоремы @th:heller-localization-k0 позволяет
  описать приведенным выше способом отображение $partial=phi^(-1) partial'$, что
  и требовалось доказать.
]

#corollary[
  В ситуации следствия @cor:localization-k-sequence предположим, что категория
  $bold(C)'$ полупроста и что выполнено одно из условий
  @cond:localization-devissage-hypothesis или
  #[@cond:localization-resolution-hypothesis]:
  #condition-list[
    #condition-item(format: "cyrillic")[категория $bold(C)$ абелева, и каждый
      объект категории $bold(A)$ обладает конечной
      $bold(C)$-фильтрацией;] <cond:localization-devissage-hypothesis>

    #condition-item(format: "cyrillic")[каждый объект категории $bold(A)$
      обладает конечной $bold(C)$-резольвентой.]
    <cond:localization-resolution-hypothesis>
  ]
  #source(336)Тогда функторы $bold(S) subset bold(A) -> bold(A)'$ индуцируют
  точную последовательность
  $
    K_1 (bold(A)') arrow.r^(overline(partial)) K_0 (bold(S))
    arrow.r^(overline(d)) K_0 (bold(A)) -> K_0 (bold(A)') -> 0.
  $
] <cor:localization-devissage-resolution-sequence>

#proof[
  Коммутативный квадрат
  $ #localization-exact-functor-square() $
  приводит нас к коммутативной диаграмме
  $ #localization-exact-comparison() $
  Следствие @cor:localization-k-sequence обеспечивает точность обеих строк,
  кроме, возможно, места $K_0 (bold(S))$. Точность в этом месте для нижней
  строки следует из полупростоты категории $bold(C)'$ (теорема
  @th:semisimple-exact-k-sequence @cond:semisimple-target-exact-k-sequence). Так
  как $overline(d) overline(partial)=0$, то точность верхней строки в
  $K_0 (bold(S))$ будет установлена, если мы будем знать, что $h$ — мономорфизм.
  Но это следует из теоремы @th:devissage-k-isomorphisms в случае
  @cond:localization-devissage-hypothesis и из теоремы
  @th:grothendieck-resolution-k0 в случае
  @cond:localization-resolution-hypothesis, что и требовалось доказать.
]

Мы закончим этот параграф результатом, который по идее близок к теореме
@th:heller-localization-k0, а его доказательство требует несколько больше
техники.

#theorem[
  Пусть диаграмма
  $ #localization-exact-functor-square(projective: true) $
  коммутативна, причем $overline(S)$ — функтор факторизации. Допустим, что:
  #condition-list[
    #condition-item[объекты в $bold(P)$ и $bold(P)'$ проективны, а функтор $S$
      кофинален;] <cond:projective-localization-cofinal>

    #condition-item[если $f:P -> Q$ — морфизм из категории $bold(A)$, для
      которого $P in bold(P)$ и $overline(S) f$ — мономорфизм, то $f$ —
      мономорфизм;] <cond:projective-localization-reflects-monomorphisms>

    #condition-item[если $P in bold(P)$ и $Q subset P$, причем
      $P slash Q in bold(S)$, то существует объект $P' subset Q$, для которого
      $P' in bold(P)$ и $P slash P' in bold(S)$.]
    <cond:projective-localization-small-subobjects>
  ]
  Пусть $bold(H)$ — полная подкатегория объектов $A in bold(A)$, обладающих
  конечными $bold(P)$-резольвентами. Пусть $bold(H)_bold(S)=bold(H) ∩ bold(S)$.
  Тогда последовательность
  $
    K_1 (bold(P)) -> K_1 (bold(P)') arrow.r^partial K_0 (bold(H)_bold(S))
    arrow.r^d K_0 (bold(P)) -> K_0 (bold(P)')
  $
  #source(337)точна. Здесь $d$ — композиция отображения
  $K_0 (bold(H)_bold(S)) -> K_0 (bold(H))$ и обратного отображения к
  гомоморфизму $K_0 (bold(P)) -> K_0 (bold(H))$, индуцированных вложениями
  $bold(H)_bold(S) subset bold(H)$ и $bold(P) subset bold(H)$. Отображение
  $partial$ определяется следующим образом: если $(S P,alpha) in Sigma bold(P)'$
  и диаграмма $P supset P' arrow.r^f P$ представляет $alpha$, где
  $P' in bold(P)$, то
  $partial[S P,alpha]_(bold(P)')=[Coker (f)]_(bold(H)_bold(S))
  -[P slash P']_(bold(H)_bold(S))$.
] <th:projective-localization-exact-sequence>

#proof[
  Пусть $bold(H)'$ — полная подкатегория объектов $A' in bold(A)'$, обладающих
  конечными $bold(P)'$-резольвентами. Тогда мы получаем коммутативный квадрат
  $ #localization-exact-functor-square(projective: true, resolved: true) $
  где функтор $T$ индуцирован функтором $overline(S)$ (функтор $T$ определен,
  поскольку функтор $overline(S)$ точный). Итак, получили коммутативную
  диаграмму
  $ #localization-exact-comparison(projective: true) $
  в которой в силу теоремы @th:projective-resolution-k-isomorphisms и
  предложения @prop:relative-projective-resolution-k0 все вертикальные
  отображения являются изоморфизмами. Кроме того, так как категория $bold(P)$
  полупроста и функтор $S$ кофинален, то из теоремы
  @th:semisimple-exact-k-sequence следует, что нижняя строка точна.
  Следовательно, и верхняя строка также точна.

  Докажем теорему, построив изоморфизмы $phi$ и $psi$, для которых диаграмма
  $
    #localization-k0-triangle()
  $ <eq:projective-localization-isomorphism-triangle>
  коммутативна, а отображения $d=-d' psi^(-1)$ и $partial=psi partial'$
  допускают описание, приведенное в теореме.

  Функтор $F:bold(H)_bold(S) -> italic("co")(T)$, для которого $F(A)=(0,0,A)$,
  точен. Поэтому он индуцирует гомоморфизм
  $phi:K_0 (bold(H)_bold(S)) -> K'_0 (T)$. Кроме того,
  $d'' phi[A]_(bold(H)_bold(S))=d''[0,0,A]_T=-[A]_(bold(H))$. Следовательно,
  отображение $-d'' phi$ индуцировано вложением
  $bold(H)_bold(S) subset bold(H)$.

  Построим отображение $psi$. Пусть $(P,alpha,Q) in italic("co")(S)$.
  #condition-list[
    #condition-item[_Отображение $alpha$ допускает представление диаграммой
      $P supset P' arrow.r^f Q$, где $P' in bold(P)$ и $f$ — мономорфизм._
      Действительно, пусть #source(338)$P supset P' arrow.r^(f') Q' arrow.l^b Q$
      — любое представление, и пусть $b$ — эпиморфизм. В условии
      @cond:projective-localization-small-subobjects говорится, что можно
      выбрать $P'$ меньше, если необходимо, и считать, что $P' in bold(P)$.
      Тогда из условия @cond:projective-localization-reflects-monomorphisms
      следует, что $b$ и $f'$ — мономорфизмы, так как $S b$ и $S f'$ —
      изоморфизмы. Следовательно, можно заменить $Q'$ на $Q$, $b$ на $1_Q$ и
      $f'$ на $f=b^(-1) f'$.] <cond:projective-localization-psi-representation>

    #condition-item[_Отображение
      $psi(P, alpha, Q)=[Q slash f P']_(bold(H)_bold(S))
      -[P slash P']_(bold(H)_bold(S))$ определено корректно._
      Действительно, пусть $P supset P'_i arrow.r^(f_i) Q$ ($i=0,1$) — два
      представления (как в @cond:projective-localization-psi-representation)
      морфизма $alpha$. Из рассмотрения последовательности
      $0 -> P'_0 ∩ P'_1 -> P -> (P slash P'_0) plus.o (P slash P'_1)$
      следует, что $P slash (P'_0 ∩ P'_1) in bold(S)$. В силу условия
      @cond:projective-localization-small-subobjects найдем объект
      $P' subset P'_0 ∩ P'_1$, такой, что $P' in bold(P)$ и
      $(P slash P') in bold(S)$. Пусть морфизм $g_i:P' -> Q$ индуцирован
      отображением $f_i$ ($i=0,1$). Так как $S g_0=S g_1$, то существует морфизм
      $g':Q -> Coker (g_0-g_1)$, для которого $S g'$ — изоморфизм.
      Следовательно, в силу условия
      @cond:projective-localization-reflects-monomorphisms $g'$ — мономорфизм и
      поэтому $g_0=g_1$ (обозначим этот морфизм через $f$). Тогда в группе
      $K_0 (bold(H)_bold(S))$ справедливы следующие равенства:
      $
        [Q slash f P']-[P slash P']
        =[Q slash f_i P'_i]+[f_i P'_i slash f_i P']
        -[P slash P'_i]-[P'_i slash P']
        =[Q slash f_i P'_i]-[P slash P'_i] quad (i=0,1),
      $
      поскольку $f_i P'_i slash f_i P' tilde.eq P'_i slash P'$.]
    <cond:projective-localization-psi-well-defined>

    #condition-item[_Если $(P_i,alpha_i,Q_i) in italic("co")(S)$ ($i=0,1$), то_
      $
        psi(P_0 plus.o P_1, alpha_0 plus.o alpha_1, Q_0 plus.o Q_1)
        =psi(P_0, alpha_0, Q_0)+psi(P_1, alpha_1, Q_1).
      $
      В этом легко убедиться, поскольку если диаграмма
      $P_i supset P'_i arrow.r^(f_i) Q_i$ представляет $alpha_i$ ($i=0,1$), как
      в @cond:projective-localization-psi-representation, то диаграмма
      $P_0 plus.o P_1 supset P'_0 plus.o P'_1
      arrow.r^(f_0 plus.o f_1) Q_0 plus.o Q_1$
      дает такое же представление для $alpha_0 plus.o alpha_1$.]
    <cond:projective-localization-psi-additivity>

    #condition-item[_Если $(P,alpha,Q),(Q,beta,R) in italic("co")(S)$, то_
      $ psi(P, beta alpha, R)=psi(P, alpha, Q)+psi(Q, beta, R). $
      Сначала выберем представление $Q supset Q' arrow.r^g R$ морфизма $beta$
      (как в @cond:projective-localization-psi-representation). Далее будем
      искать такое же представление $P supset P' arrow.r^f Q$ для $alpha$, с тем
      чтобы $f P' subset Q'$. Если это не так, то можно выбрать меньшее $P'$,
      для которого это уже будет иметь место. Так как
      $f P' slash (f P' ∩ Q') subset Q slash Q'
      in bold(S)$, то можно использовать условие
      @cond:projective-localization-small-subobjects и найти $P'' subset P'$,
      $P'' in bold(P)$, для которого $f P'' subset f P' ∩ Q'$ (напомним, что $f$
      — мономорфизм) и $P' slash P'' in bold(S)$. Мы можем теперь заменить $P'$
      на $P''$, желая добиться выполнения сформулированного выше условия. Таким
      образом, получаем представление $P supset #source(339)P'
      arrow.r^(g f') R$ морфизма $beta alpha$, где отображение $f':P' -> Q'$
      индуцировано с помощью $f$. Следовательно,
      $
        psi(P, beta alpha, R)=[R slash g f' P']-[P slash P']
        =[R slash g Q']+[g Q' slash g f' P']-[P slash P']
        =[R slash g Q']-[Q slash Q']+[Q slash Q']+[Q' slash f P']-[P slash P'].
      $
      ($g$ — мономорфизм, и поэтому
      $g Q' slash g f' P' tilde.eq Q' slash f' P'=Q' slash f P'$)
      $
        =psi(Q, beta, R)+[Q slash f P']-[P slash P']
        =psi(Q, beta, R)+psi(P, alpha, Q).
      $
    ] <cond:projective-localization-psi-composition>
  ]

  Из всего этого следует, что отображение $psi$ индуцирует гомоморфизм
  $psi:K'_0 (S) -> K_0 (bold(H)_bold(S))$. При доказательстве утверждения
  @cond:projective-localization-psi-additivity мы ограничились лишь
  рассмотрением прямых сумм, а не всех точных последовательностей; это позволила
  сделать теорема @th:semisimple-exact-k-sequence
  @cond:semisimple-exact-k-full-sequence в силу того, что категория $bold(P)$
  полупроста. Если вспомнить, что $partial'[S P,alpha]_(bold(P)')=[P,alpha,P]_S$
  для $(S P,alpha) in Sigma bold(P)'$, то станет очевидно, что отображение
  $partial=psi partial'$ допускает приведенное в теореме описание.

  Чтобы показать, что $phi$ и $psi$ — изоморфизмы (и тем самым закончить
  доказательство теоремы), проверим, что в диаграмме
  @eq:projective-localization-isomorphism-triangle справедливо равенство
  $h=phi psi$ и что $psi h^(-1) phi$ — тождественное отображение на группе
  $K_0 (bold(H)_bold(S))$. Это достаточно, поскольку $h$ — изоморфизм.

  _Доказательство равенства $h=phi psi$._
  Если $(P,alpha,Q) in italic("co")(S)$, то, как и в
  @cond:projective-localization-psi-representation, выберем представление
  $P supset P' arrow.r^f Q$ отображения $alpha$. Тогда
  $[P,alpha,Q]=[P',S f,Q]-[P',S j,P]$ в группе $K'_0 (S)$, где $j$ — вложение
  объекта $P'$ в $P$. Следовательно, достаточно показать, что если $f:P -> Q$ —
  мономорфизм в категории $bold(P)$, для которого $S f$ — изоморфизм, то
  $phi psi[P,S f,Q]=h[P,S f,Q]$. Заметим сначала, что $phi psi[P,S f,Q]_S
  =phi([Q slash f P]_(bold(H)_bold(S)))=[0,0,Q slash f P]_T$. С другой стороны,
  рассмотрение точной последовательности
  $
    0 -> (P,1_(S P),P) arrow.r^((1,f)) (P,S f,Q)
    -> (0,0,Q slash f P) -> 0
  $
  в категории $italic("co")(T)$ показывает, что
  $ h[P,S f,Q]_S=[P,S f,Q]_T=[0,0,Q slash f P]_T. $

  _Доказательство того, что $psi h^(-1) phi$ — тождественное отображение группы
  $K_0 (bold(H)_bold(S))$._ Начнем с леммы.
]

#lemma[
  Пусть $bold(H)_bold(S)^1 subset bold(H)_bold(S)$ — полная подкатегория,
  объекты которой обладают $bold(P)$-резольвентами длины $<=1$. Тогда каждый
  объект категории $bold(H)_bold(S)$ обладает конечной
  $bold(H)_bold(S)^1$-резольвентой, а следовательно, указанное вложение
  индуцирует изоморфизм $K_0 (bold(H)_bold(S)^1) -> K_0 (bold(H)_bold(S))$.
] <lem:torsion-resolution-length-one-devissage>
#symbol-idx($bold(H)_bold(S)^1$, sort: "H_S^1", group: "categories", order: 13)

#source(340)
#proof[
  Если $A in bold(H)$, то через $d(A)$ обозначим длину самой короткой
  $bold(P)$-резольвенты объекта $A$. Если $A in bold(H)_bold(S)$, то покажем,
  проводя индукцию по $d(A)$, что объект $A$ обладает конечной
  $bold(H)_bold(S)^1$-резольвентой. Случай $d(A)<=1$ тривиален. Поэтому
  предположим, что $d(A)>1$. Выберем точную последовательность
  $0 -> B -> P -> A -> 0$, где $P in bold(P)$. Условие
  @cond:projective-localization-small-subobjects теоремы говорит нам о
  существовании объекта $P' subset B$, $P' in bold(P)$, для которого
  $P slash P' in bold(S)$. Следовательно, мы получаем точную последовательность
  $0 -> B slash P' -> P slash P' -> A -> 0$ в категории $bold(S)$. Очевидно, что
  $d(P slash P')<=1$. Так как $d(A)>1$, то из
  @prop:projective-dimension-sequence следует, что $d(B slash P')<d(A)$. Таким
  образом, объект $B slash P'$ обладает конечной
  $bold(H)_bold(S)^1$-резольвентой (в силу индуктивного предположения), а тогда
  этим свойством обладает и объект $A$. Последнее утверждение леммы вытекает
  теперь из теоремы @th:grothendieck-resolution-k0, что и требовалось доказать.
]

В силу леммы достаточно показать, что
$psi h^(-1) phi[A]_(bold(H)_bold(S))=[A]_(bold(H)_bold(S))$, где $d(A)<=1$.
Выберем резольвенту $0 -> P_1 arrow.r^f P_0 -> A -> 0$, $P_i in bold(P)$. Тогда
мы получим $italic("co")(S)$-резольвенту объекта $(0,0,A) in italic("co")(T)$:
$
  0 -> (P_1,1_(S P_1),P_1) arrow.r^((1,f)) (P_1,S f,P_0)
  -> (0,0,A) -> 0.
$
Таким образом, $h^(-1) phi[A]_(bold(H)_bold(S))
=h^(-1)([0,0,A]_T)=[P_1,S f,P_0]_S$. Наконец,
$psi[P_1,S f,P_0]_S=[P_0 slash f P_1]_(bold(H)_bold(S))
=[A]_(bold(H)_bold(S))$, что и требовалось доказать.

#theorem[
  В ситуации теоремы @th:projective-localization-exact-sequence предположим, что
  каждый объект категории $bold(S)$ обладает конечной $bold(P)$-резольвентой, т.
  е. что $bold(S)=bold(H)_bold(S)$. Пусть $bold(H)'$ — полная подкатегория
  объектов $A' in bold(A)'$, обладающих конечными $bold(P)'$-резольвентами.
  Тогда:
  #condition-list[
    #condition-item(format: "cyrillic")[если $A in bold(A)$, то
      $A in bold(H) <=> overline(S) A in bold(H)'$;]
    <cond:localization-finite-resolution-reflection>

    #condition-item(format: "cyrillic")[последовательность
      $
        K_1 (bold(P)) -> K_1 (bold(P)') arrow.r^partial K_0 (bold(S))
        -> K_0 (bold(P)) -> K_0 (bold(P)') -> 0
      $
      точна.] <cond:localization-projective-k0-surjection>
  ]
] <th:localization-finite-resolution-sequence>

#proof[
  @cond:localization-finite-resolution-reflection Если $P -> A$ — конечная
  $bold(P)$-резольвента, то $overline(S) P -> overline(S) A$ — конечная
  $bold(P)'$-резольвента, поэтому $overline(S) A in bold(H)'$. Для
  доказательства обратного утверждения пусть $overline(S) A in bold(H)'$. Через
  $d'(overline(S) A)$ обозначим минимальную длину $bold(P)'$-резольвенты объекта
  $overline(S) A$. Проводя индукцию по $d'(overline(S) A)$, покажем, что
  $A in bold(H)$. Следующие замечания будут использоваться неоднократно. Пусть
  $0 -> B' -> B -> B'' -> 0$ — точная последовательность в категории $bold(A)'$.
  Если два объекта из $B',B,B''$ лежат в $bold(H)'$, то там же лежит и третий.
  Кроме того, если $d'(B)<d'(B'')$, то $d'(B')<d'(B'')$. Эти и аналогичные им
  свойства категорий $bold(P)$ и $bold(H)$ вытекают из
  @prop:projective-dimension-sequence.

  #source(341)_Случай $d'(overline(S) A)=0$._ В этой ситуации объект
  $overline(S) A$ изоморфен объекту категории $bold(P)'$. Так как функтор
  $S:bold(P) -> bold(P)'$ кофинален, то
  $overline(S) A plus.o overline(S) B tilde.eq S P$ для некоторых объектов
  $B in bold(A)$ и $P in bold(P)$. Заменяя $A$ на $A plus.o B$, можно считать,
  что существует изоморфизм $alpha:S P -> overline(S) A$, где $P in bold(P)$.
  Пусть $P supset P' arrow.r^f A' arrow.l^a A$ — представление отображения
  $alpha$, где $a$ — эпиморфизм. Используя условие
  @cond:projective-localization-small-subobjects из
  @th:projective-localization-exact-sequence, можно считать далее, что
  $P' in bold(P)$. Так как $overline(S) f$ — изоморфизм, то условие
  @cond:projective-localization-reflects-monomorphisms из
  @th:projective-localization-exact-sequence влечет за собой точность
  последовательности $0 -> P' arrow.r^f A' -> Coker (f) -> 0$. Поскольку
  $Coker (f) in bold(S) subset bold(H)$, то $A' in bold(H)$. Так как
  $Ker (a) in bold(S)$ и последовательность
  $0 -> Ker (a) -> A arrow.r^a A' -> 0$ точна, то $A in bold(H)$.

  _Случай $d'(overline(S) A)>0$._
  Любой объект из $bold(P)'$ можно поднять до объекта из $bold(A)$ (но не
  обязательно из $bold(P)$). Таким образом, можно найти такой эпиморфизм
  $overline(S) B -> overline(S) A$ для некоторого $B in bold(A)$, такого, что
  $overline(S) B in bold(P)'$. Представим $overline(f)$ в виде
  $B arrow.l^b B' arrow.r^(f') A=A$. Так как $overline(S) b$ — изоморфизм, то
  можно заменить $B$ на $B'$. Тогда допустим, что морфизм $f:B -> A$ таков, что
  $overline(S) B in bold(P)'$ и $overline(S) f$ — эпиморфизм. Пусть $C=Ker f$.
  Из точности последовательности
  $0 -> overline(S) C -> overline(S) B -> overline(S) A -> 0$ следует, что
  $d'(overline(S) C)<d'(overline(S) A)$. Таким образом, учитывая наше
  индуктивное предположение и разобранный случай $d'=0$, получаем, что
  $C,B in bold(H)$. Из точности последовательности $0 -> C -> B -> Im (f) -> 0$
  следует, что $Im (f) in bold(H)$. Наконец, рассмотрение последовательности
  $0 -> Im (f) -> A -> Coker (f) -> 0$ показывает, что $A in bold(H)$, так как
  $Coker (f) in bold(S) subset bold(H)$.

  @cond:localization-projective-k0-surjection Выписанная точная
  последовательность в точности совпадает с точной последовательностью теоремы
  @th:projective-localization-exact-sequence (за исключением утверждения о том,
  что отображение $K_0 (bold(P)) -> K_0 (bold(P)')$ сюръективно). Но это
  отображение изоморфно соответствующему отображению
  $K_0 (bold(H)) -> K_0 (bold(H)')$. Часть
  @cond:localization-finite-resolution-reflection утверждает, что отображение
  $bold(H) -> bold(H)'$ сюръективно на объектах, что и требовалось доказать.
]
