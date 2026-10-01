#import "main-defs.typ": (
  Aut, E, End, K, Pic, Rk, SK, U, det, idx, maxSpec, mennicke, rk, source,
  symbol-idx, tensor,
)
#import "statements.typ": proof, proposition

== Последовательность для локализации дедекиндова кольца
<sec:dedekind-localization-sequence>

#source(533)
Пусть $A$ — дедекиндово кольцо с полем частных $L=S^(-1)A$, где
$S=A without {0}$. Точная последовательность для локализации $A -> L$ такова:
$
  K_1 (A) -> K_1 (L) -> K_0 (bold(italic(M))_S (A)) -> K_0 (A)
  -> K_0 (L) -> 0
$ <eq:dedekind-localization-sequence>
(см. @th:k-localization-boundary). Здесь $bold(italic(M))_S (A)$ — категория
конечно порожденных периодических $A$-модулей, и в силу метода «отщипывания»
(гл.~@ch:abelian-k-theory, §~@sec:devissage) мы получаем, что
#idx("метод отщипывания")
$
  K_i (bold(italic(M))_S (A))=
  product.co_(frak(p) in maxSpec(A)) K_i (A slash frak(p)).
$
Последовательность @eq:dedekind-localization-sequence приводит нас к вопросу:
будет ли последовательность
$ K_1 (bold(italic(M))_S (A)) -> K_1 (A) -> K_1 (L) $
также точной. Поскольку композиция отображений равна нулю, то вопрос об
эквивалентности форм звучит так: будет ли естественный гомоморфизм
$ K_1 (bold(italic(M))_S (A)) -> SK_1 (A) $ <eq:dedekind-torsion-sk1-map>
сюръективным. Этот вопрос интересен, в частности, и потому, что группа
$SK_1 (A)$ может быть интерпретирована в терминах «законов взаимности» (см.
гл.~@ch:mennicke-symbols). Мы покажем, что отображение
@eq:dedekind-torsion-sk1-map действительно сюръективно. Это будет сделано в
терминах символов Меннике. В следующем параграфе эта информация будет
использована для описания поведения законов взаимности при переходе от $A$ к его
целому замыканию в конечном расширении поля $L$.

Пусть $frak(q)$ — ненулевой идеал кольца $A$. Через $bold(italic(M))(A,frak(q))$
обозначим полную подкатегорию в категории $bold(italic(M))(A)$, объекты которой
без «$frak(q)$-кручения».
#symbol-idx(
  $bold(italic(M))(A,frak(q))$,
  sort: "M(A,q)",
  group: "categories",
  order: 16,
)
То есть $M in bold(italic(M))(A,frak(q))$, если ни один ненулевой элемент в $M$
не аннулируется идеалом $frak(q)$. Важность этого условия для наших целей
объясняется следующим: если последовательность
$ E=(0 -> M' -> M -> M'' -> 0) $
точна в $bold(italic(M))(A,frak(q))$, то последовательность
$E tensor_A (A slash frak(q))$ также точна. Далее, введем в рассмотрение
$
  bold(italic(M))_S (A,frak(q))=
  bold(italic(M))(A,frak(q)) inter bold(italic(M))_S (A).
$

#source(534)
В силу метода «отщипывания» (@th:devissage-k-isomorphisms) получаем
$
  K_i (bold(italic(M))_S (A,frak(q)))=
  product.co_(frak(p) in maxSpec(A),frak(p) divides.not frak(q))
  K_i (A slash frak(p)),
$ <eq:dedekind-qfree-devissage>
поскольку категория полупростых модулей в $bold(italic(M))_S (A,frak(q))$
является прямой суммой категорий
$bold(italic(M))(A slash frak(p))$
($frak(p) in maxSpec(A), frak(p) divides.not frak(q)$).

Можно вычислить группу $K_1 (A,frak(q))$ по категории
$Sigma(bold(P)(A), frak(q))$, объектами которой являются пары $(P,alpha)$, где
$P in bold(P)(A)$ и $alpha in Aut_A (P,frak(q))$, т.~е.
$alpha tensor_A (A slash frak(q))=1_(P tensor_A (A slash frak(q)))$. Аналогично
можно определить категорию $Sigma(bold(italic(M))(A,frak(q)), frak(q))$,
разрешая $P$ пробегать объекты категории $bold(italic(M))(A,frak(q))$.

#proposition[
  $Sigma(bold(italic(M))(A,frak(q)), frak(q))$ — допустимая подкатегория в
  категории $Sigma bold(italic(M))(A)$. Вложение
  $Sigma(bold(P)(A), frak(q)) subset
  Sigma(bold(italic(M))(A,frak(q)), frak(q))$ индуцирует изоморфизм
  $
    K_1 (A,frak(q)) -> K_1 (bold(italic(M))(A,frak(q)),frak(q)),
  $ <eq:dedekind-relative-resolution-isomorphism>
  где правая группа определяется соотношениями, которые аналогичны
  использованным соотношениям в определении обычного функтора $K_1$.
] <prop:dedekind-qfree-relative-resolution>

#proof[
  Единственное нетривиальное место в первом утверждении: если последовательность
  $ 0 -> (M',alpha') -> (M,alpha) -> (M'',alpha'') -> 0 $
  точна в $Sigma bold(italic(M))(A)$ и если
  $(M,alpha),(M'',alpha'') in Sigma(bold(italic(M))(A,frak(q)), frak(q))$, то
  $(M',alpha') in Sigma(bold(italic(M))(A,frak(q)), frak(q))$. Сначала заметим,
  что $M' in bold(italic(M))(A,frak(q))$, поскольку $M$ без $frak(q)$-кручения.
  Остается проверить, что $alpha'=I mod frak(q)$. Но так как
  $M'' in bold(italic(M))(A,frak(q))$, то последовательность
  $
    (M',alpha') tensor_A (A slash frak(q)) ->
    (M,alpha) tensor_A (A slash frak(q))
  $
  точна. Поскольку $alpha tensor_A (A slash frak(q))=I$, то это же верно и для
  ограничения $alpha' tensor_A (A slash frak(q))$ на
  $M' tensor_A (A slash frak(q))$.

  Чтобы убедиться в том, что отображение
  @eq:dedekind-relative-resolution-isomorphism — изоморфизм, достаточно в силу
  @th:relative-resolution-k1 показать, что для $M in bold(italic(M))(A,frak(q))$
  найдется эпиморфизм $P -> M$, где $P in bold(P)(A)$, для которого любой
  автоморфизм $alpha in Aut_A (M,frak(q))$ можно поднимать до элемента группы
  $Aut_A (P,frak(q))$.

  Пусть $f:Q -> M$ — эпиморфизм и $Q in bold(P)(A)$. Положим $P=Q plus.o Q$.
  Построим $epsilon in E(Q,Q;frak(q))$, для которого
  $
    (P,epsilon)=(Q plus.o Q,epsilon) arrow.r^(f plus.o f)
    (M plus.o M,alpha plus.o alpha^(-1)) arrow.r^((1_M,0)) (M,alpha)
  $
  является последовательностью морфизмов в категории
  $Sigma(bold(italic(M))(A,frak(q)), frak(q))$. В частности, $epsilon$ окажется
  требуемым нам поднятием автоморфизма $alpha$.

  #source(535)Положим $h_+=1-alpha$ и $h_-=1-alpha^(-1)$. Мы получили
  эндоморфизмы модуля $M$, образы которых лежат в $M frak(q)$. Кроме того (см.
  доказательство @prop:projective-automorphism-lifts),
  $
    mat(alpha, 0; 0, alpha^(-1))=
    mat(1, 0; 1, 1) mat(1, 0; -h_-, 1) mat(1, h_+; 0, 1)
    mat(1, 0; -1, 1) mat(1, h_-; 0, 1)
  $
  $
    =epsilon_21 (1) epsilon_21 (-h_-) epsilon_12 (h_+)
    epsilon_21 (1)^(-1) epsilon_12 (h_-),
  $
  где $epsilon_(i j) (t)=I+t e_(i j)$. Используя эпиморфизм $f:Q -> M$, можно
  поднять $h_±$ до эндоморфизма $g_±$ модуля $Q$, образ которого будет лежать в
  $Q frak(q)$ (в силу проективности модуля $Q$). Таким образом, искомое поднятие
  $epsilon in E(Q,Q;frak(q))$ задается формулой
  $
    epsilon=epsilon_21 (1) epsilon_21 (-g_-) epsilon_12 (g_+)
    epsilon_21 (1)^(-1) epsilon_12 (g_-),
  $
  где, конечно, $1$ теперь означает $1_Q$, и т.~д. Это завершает доказательство.
]

#proposition[
  Вложение $bold(italic(M))_S (A,frak(q)) subset bold(italic(M))(A,frak(q))$
  индуцирует гомоморфизм
  $ K_1 (bold(italic(M))_S (A,frak(q))) -> K_1 (A,frak(q)), $
  <eq:dedekind-torsion-relative-k1-map>
  образ которого совпадает с $SK_1 (A,frak(q))$. К тому же
  $
    K_1 (bold(italic(M))_S (A,frak(q))) approx
    product.co K_1 (A slash frak(p)) approx product.co U(A slash frak(p)),
  $
  где $frak(p)$ пробегает все максимальные идеалы, не делящие $frak(q)$.
  Используя это отождествление, можно сказать, что гомоморфизм
  $U(A slash frak(p)) -> SK_1 (A,frak(q))$, индуцированный отображением
  @eq:dedekind-torsion-relative-k1-map, определен так:
  $
    u mapsto mennicke(frak(p) frak(q), a), quad
    "где" quad a equiv 1 mod frak(q), quad a equiv u mod frak(p),
  $
  а символ является символом Меннике (см. гл.~@ch:mennicke-symbols,
  §§~@sec:mennicke-main-theorems, @sec:relative-mennicke-symbols).
] <prop:dedekind-torsion-mennicke-surjection>

*Замечание.* Из теорем §~@sec:dedekind-reciprocity-laws гл.~@ch:mennicke-symbols
мы получаем теперь, что отображение @eq:dedekind-torsion-relative-k1-map в
сущности является универсальной $frak(q)$-взаимностью.

#proof[
  Сначала проверим последнее утверждение. Если $u in U(A slash frak(p))$, то
  указанное выше отождествление переводит $u$ в
  $[A slash frak(p),u]_S in K_1 (bold(italic(M))_S (A,frak(q)))$. Тот факт, что
  $frak(p)$ не делит $frak(q)$, обеспечивает включение
  $A slash frak(p) in bold(italic(M))_S (A,frak(q))$. В принятых нами
  обозначениях символы $u$ и $u dot 1_(A slash frak(p))$ не различались.

  Выберем идеал $frak(c)$ взаимно простым с $frak(p) frak(q)$ и так, чтобы
  $frak(p) frak(c)=b A$ являлся главным идеалом. Тогда
  $
    [A slash frak(p),u]_S=[A slash frak(p),u]_S+[A slash frak(c),1]_S
    =[A slash (b A),v]_S
  $
  для некоторого $v in U(A slash (b A))$, $v equiv u mod frak(p)$,
  $v equiv 1 mod frak(c)$. Выберем $a in A$ так, что $a equiv v mod b A$,
  $a equiv 1 mod frak(q)$. Тогда $a equiv 1 mod frak(c) frak(q)$ #source(536)и
  потому
  $
    mennicke(frak(p) frak(q), a)=
    mennicke(frak(p) frak(q), a) mennicke(frak(c) frak(q), a)
    =mennicke(b frak(q), a).
  $
  Следовательно, достаточно показать, что образ $[A slash (b A),v]$ в группе
  $K_1 (A,frak(q))$ элемента $[A slash (b A),v]_S$ равен
  $mennicke(b frak(q), a)$. Пусть элемент $a' in A$ таков, что
  $a' equiv v^(-1) mod b A$, $a' equiv 1 mod frak(q)$. Тогда, как и в
  доказательстве предложения @prop:dedekind-qfree-relative-resolution, получаем
  резольвенту
  $
    0 -> (A plus.o A,beta) arrow.r^(b 1_A plus.o 1_A)
    (A plus.o A,epsilon) arrow.r^((f,0)) (A slash (b A),v) -> 0,
  $
  где $f:A -> A slash (b A)$ — каноническая проекция. Здесь элемент
  $epsilon in E_2 (A,frak(q))$ задается равенством
  $
    epsilon=epsilon_21 (1) epsilon_21 (-a_-) epsilon_12 (a_+)
    epsilon_21 (1)^(-1) epsilon_12 (a_-),
  $
  где $a_+=1-a$ и $a_-=1-a'$. Конечно, $beta$ определяется по точной
  последовательности, из рассмотрения которой теперь следует, что
  $ [A slash (b A),v]=[A plus.o A,beta^(-1)]. $
  <eq:dedekind-torsion-resolution-class>

  Выпишем теперь матрицу $epsilon$ в явном виде:
  $
    epsilon=mat(1, 0; a', 1) mat(1, 1-a; 0, 1)
    mat(1, 0; -1, 1) mat(1, 1-a'; 0, 1)
  $
  $
    =mat(1, 1-a; a', 1+a'-a'a) mat(1, 1-a'; -1, a')
    =mat(a, 1-a a'; a'a-1, a'(2-a'a)).
  $
  Так как $epsilon equiv v plus.o v^(-1) mod b A$, то $a'a-1=b c$. Далее
  $epsilon equiv I mod frak(q)$ и $b$ взаимно просто с $frak(q)$. Поэтому
  $c in frak(q)$. Если $e_1,e_2$ — стандартный базис модуля $A plus.o A$, то
  матричное задание $beta$ получается из рассмотрения действия $epsilon$ на
  $e_1 b A plus.o e_2 A$. Такое матричное задание получается сопряжением
  матричного задания для $epsilon$ с помощью матрицы $mat(b, 0; 0, 1)$.
  Следовательно, в базисе $e_1 b,e_2$
  $
    beta=mat(b^(-1), 0; 0, 1) mat(a, 1-a a'; a'a-1, a'(2-a'a)) mat(b, 0; 0, 1)
  $
  $
    =mat(a, (1-a a')b^(-1); (a'a-1)b, a'(2-a'a))
    =mat(a, -c; (a'a-1)b, a'(2-a'a)).
  $
  Теперь из @eq:dedekind-torsion-resolution-class получаем:
  $
    [A slash (b A),v]=[A plus.o A,beta^(-1)]
    =mennicke((a'a-1)b, a)=mennicke(b frak(q), a) mennicke(a'a-1, a).
  $
  #source(537)Но
  $
    mennicke(a'a-1, a)=mennicke(a'a-1-a(a'-1), a)
    =mennicke(a-1, a)=mennicke(a-1, 1)=1.
  $
  Итак, мы доказали последнее утверждение предложения.

  Остается лишь показать, что отображение
  $ K_1 (bold(italic(M))_S (A,frak(q))) -> SK_1 (A,frak(q)) $
  <eq:dedekind-torsion-sk1-surjection>
  сюръективно. Развитая в главе @ch:mennicke-symbols теория позволяет записать
  каждый элемент группы $SK_1 (A,frak(q))$ в виде $mennicke(b, a)$, где
  $(a,b) in W_frak(q)$. Тогда
  $
    mennicke(b, a)=mennicke(b(1-a), a)=mennicke((b+t a)(1-a), a)
    =mennicke((b+t a)frak(q), a)
  $
  для любого элемента $t in A$. Выбирая подходящим образом $t$, можно считать,
  что элемент $b+t a$ взаимно прост с $frak(q)$. Тогда доказанная выше формула
  показывает, что элемент $mennicke((b+t a)frak(q), a)$ лежит в образе
  отображения @eq:dedekind-torsion-sk1-surjection, что и требовалось доказать.
]

Можно использовать предложение @prop:dedekind-torsion-mennicke-surjection для
явного описания в терминах классов идеалов и символов Меннике строения
$K_1 (A,frak(q))$ как $K_0 (A)$-модуля.

#proposition[
  Существует естественный изоморфизм $K_0 (A) approx ZZ plus.o Pic(A)$, для
  которого проекция на $ZZ$ совпадает с гомоморфизмом ранга, а $Pic(A)$ является
  идеалом, квадрат которого равен нулю. Далее, имеет место естественное
  разложение
  $ K_1 (A,frak(q))=U(A,frak(q)) plus.o SK_1 (A,frak(q)). $
  В этой координатной системе строение $K_1 (A,frak(q))$ как $K_0 (A)$-модуля
  задается следующим образом:
  $
    (n,[frak(c)]) dot (u,mennicke(frak(b), a))=
    (u^n,mennicke(frak(c) frak(q), u)^(-1) mennicke(frak(b), a)^n).
  $
  Здесь $frak(b)$ и $frak(c)$ — обратимые идеалы кольца $A$,
  $frak(b) subset frak(q)$, $a equiv 1 mod frak(q)$ и $a$ взаимно просто с
  $frak(b)$. Конечно, $n in ZZ$ и $u in U(A,frak(q))$.
] <prop:dedekind-k0-action-mennicke-coordinates>

#proof[
  Так как $A$ — дедекиндово кольцо, то $rk:Rk_0 (A) -> Pic(A)$ является
  изоморфизмом, при этом обратное к нему отображение задается так:
  $[frak(c)]_(Pic) mapsto [frak(c)]_(bold(P))-[A]_(bold(P))$ для обратимого
  идеала $frak(c)$. Утверждение о том, что $Rk_0 (A)^2=0$, следует из
  @prop:k0-support-filtration-properties
  @cond:k0-support-filtration-rank-kernel. Описанное выше действие, конечно,
  билинейно, #source(538)и поэтому для доказательства его совпадения с обычным
  действием кольца $K_0 (A)$ достаточно проверить это на аддитивных образующих
  каждого из аргументов. Следовательно, достаточно рассмотреть случай
  $
    (n,[frak(c)])=(1,[frak(p)])=[frak(p)]_(bold(P))
    quad (frak(p) in maxSpec(A)),
  $
  при этом можно считать, что $frak(p)$ не делит $frak(q)$, так как каждый класс
  идеалов содержит представитель, взаимно простой с $frak(q)$.

  Пусть $(P,alpha)$ представляет $(u,mennicke(frak(b), a))$. Поэтому
  $u=det(alpha)$. Тогда
  $
    [frak(p)]_(bold(P)) [P,alpha]=[frak(p) tensor P,1_frak(p) tensor alpha]
    =[P frak(p),beta],
  $
  где $beta=alpha|_(P frak(p))$. Получаем точную последовательность
  $ 0 -> (P frak(p),beta) -> (P,alpha) -> (P slash (P frak(p)),gamma) -> 0, $
  рассмотрение которой показывает, что
  $ [frak(p)]_(bold(P)) [P,alpha]=[P,alpha]-[P slash (P frak(p)),gamma]. $
  Так как $A slash frak(p)$ — поле, то можно действовать на
  $(P slash (P frak(p)),gamma)$ в $bold(italic(M))(A slash frak(p))$ и получить
  равенство $[P slash (P frak(p)),gamma]=[A slash frak(p),det(gamma)]$, где
  $det(gamma)$ равно образу элемента $u=det(alpha) mod frak(p)$. В силу
  @prop:dedekind-torsion-mennicke-surjection, следовательно,
  $ [A slash frak(p),det(gamma)]=mennicke(frak(p) frak(q), u). $
  Так как $[frak(p)]_(bold(P))=(1,[frak(p)])$, то
  $
    (1,[frak(p)])(u,mennicke(frak(b), a))=
    (u,mennicke(frak(b), a))-(1,mennicke(frak(p) frak(q), u))
  $
  $ = (u,mennicke(frak(p) frak(q), u)^(-1) mennicke(frak(b), a)), $
  что и требовалось доказать.
]
