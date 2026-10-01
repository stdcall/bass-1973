#import "main-defs.typ": E, GE, GL, Ker, SL, U, diag, idx, mennicke, source
#import "statements.typ": condition-item, condition-list

#heading(level: 2)[Доказательство теоремы @th:universal-mennicke-symbol-sk1. I.
  Теорема Куботы] <sec:kubotas-theorem>

Пусть кольцо $A$ и идеал $frak(q)$ удовлетворяют условиям теоремы
@th:universal-mennicke-symbol-sk1 и отображение $k: GL_2 (A, frak(q)) -> C$
определяется следующим образом:

$ k(alpha) = mennicke(b, a), quad "если" quad alpha = mat(a, b; c, d), $

#source(243)где $[ ]$ — символ Меннике. Докажем в несколько шагов, что $k$ —
гомоморфизм, обладающий свойствами, описанными в
@ss:kubota-mennicke-homomorphism.

#condition-list[
  #condition-item[
    _Если $alpha = mat(a, b; c, d) in GL_2 (A, frak(q))$, то_
    $ k(alpha) = mennicke(c, d) = mennicke(b, d)^(-1) = mennicke(c, a)^(-1). $

    Действительно, $u = a d - b c in U(A)$, и поэтому, используя
    @prop:mennicke-symbol-elementary-properties @cond:mennicke-unit-symbol,
    получаем
    $
      k(alpha) = mennicke(b, a) = mennicke(b, a d) mennicke(b, d)^(-1)
      = mennicke(b, d)^(-1) mennicke(b c, d) = mennicke(c, d)
      = mennicke(b c, a) mennicke(c, a)^(-1) = mennicke(c, a)^(-1).
    $
  ] <cond:kubota-four-matrix-entries>

  Пусть $H = {alpha in GL_2 (A, frak(q)) | k(alpha' alpha) = k(alpha') k(alpha)
    "для всех" quad alpha' in GL_2 (A, frak(q))}$, и пусть
  $N = {tau in GL_2 (A) | k(alpha^tau) = k(alpha)
    "для всех" quad alpha in GL_2 (A, frak(q))}$. Тогда, как и в
  @lem:linear-character-multiplicativity-normalizer, $H$ и $N$ — группы; при
  этом $N$ нормализует $H$.

  #condition-item[
    _$GE_2 (A) subset N$ и $GE_2 (A, frak(q)) subset H$. В действительности
    $k(alpha epsilon) = k(alpha)$ для $epsilon in GE_2 (A, frak(q))$._

    Пусть $alpha = mat(a, b; c, d) in GL_2 (A, frak(q))$, и пусть
    $epsilon_(i j) (t) = I + t e_(i j)$. Если $t in frak(q)$, то
    $alpha epsilon_(1 2) (t) = mat(a, b + t a; ast, ast)$ и
    $alpha epsilon_(2 1) (t) = mat(a + t b, b; ast, ast)$, а потому
    $k(alpha epsilon_(1 2) (t)) = mennicke(b + t a, a) = mennicke(b, a)
    = k(alpha)$. Аналогично, $epsilon_(2 1) (t) in H$.

    Для любого элемента $t in A$ справедливы равенства
    $alpha^(epsilon_(1 2) (t)) = mat(a - c t, ast; c, ast)$ и
    $alpha^(epsilon_(2 1) (t)) = mat(a + t b, b; ast, ast)$. Следовательно,
    $k(alpha^(epsilon_(1 2) (t))) = mennicke(c, a - c t)^(-1)
    = mennicke(c, a)^(-1) = k(alpha)$. Аналогично $epsilon_(2 1) (t) in N$.

    Если $delta = diag(1, u)$, то $alpha^delta = mat(a, b u; ast, ast)$ и
    $alpha delta = mat(a, b u; ast, ast)$ и, значит,
    $
      k(alpha^delta) = mennicke(b u, a) = mennicke(b u (1 - a), a)
      = mennicke(b, a) mennicke(u (1 - a), a) = mennicke(b, a) = k(alpha).
    $
    Также если $u in U(A, frak(q))$, то $k(alpha delta) = k(alpha)$.

    Так как элементы $epsilon_(1 2) (t)$, $epsilon_(2 1) (t)$ ($t in A$) и
    $delta$ порождают группу $GE_2 (A)$, то $GE_2 (A) subset N$. Поскольку $N$
    нормализует $H$ и все элементы $epsilon_(1 2) (t)$, $epsilon_(2 1) (t)$
    ($t in frak(q)$) лежат в $H$, имеем также $E_2 (A, frak(q)) subset H$.
    Наконец, так как группа $GE_2 (A, frak(q))$ порождается подгруппой #source(
      244,
    )$E_2 (A, frak(q))$ и элементами $delta$, у которых $u in U(A, frak(q))$, то
    $GE_2 (A, frak(q)) subset H$.
  ] <cond:kubota-elementary-invariance>

  #condition-item[
    _Предположим, что матрицы $alpha = mat(a, b; c, d)$ и
    $alpha' = mat(a', b'; c', d')$ из группы $GL_2 (A, frak(q))$ таковы, что
    $d equiv 1 equiv a' mod t$ для некоторого элемента $t in frak(q)$ и
    $a' A + d A = A$. Тогда $k(alpha' alpha) = k(alpha') k(alpha)$._

    Допустим, что $(a', x y) in W_frak(q)$, где $y in frak(q)$. Тогда
    $
      mennicke(x y, a') = mennicke(x y, a') mennicke(t, a')
      = mennicke(x y t, a') = mennicke(y, a') mennicke(x t, a').
    $
    Аналогичное замечание применимо к элементу $d$.

    Таким образом, $alpha' alpha
    = mat(a' a + b' c, a' b + b' d; ast, ast)$, и, следовательно,
    $
      k(alpha' alpha) = mennicke(a' b + b' d, a' a + b' c)
      = mennicke(a' b + b' d, (a' a + b' c) d)
      mennicke(a' b + b' d, d)^(-1)
      = mennicke(a' b + b' d, a' u + c(a' b + b' d))
      mennicke(a' b, d)^(-1)
      = mennicke(a' b + b' d, a' u)
      mennicke(a' t, d)^(-1) mennicke(b, d)^(-1)
      = mennicke(b' d, a' u) mennicke(a' t, d)^(-1) k(alpha)
      = mennicke(b' d, u) mennicke(b', a') mennicke(d t, a')
      mennicke(a' t, d)^(-1) k(alpha)
      = k(alpha') mennicke(d t, a') mennicke(a' t, d)^(-1) k(alpha)
      = k(alpha') k(alpha).
    $
    Здесь $a' A + d A = A$, и поэтому $(d, a' b) in W_frak(q)$;
    $u = a d - b c in U(A, frak(q))$. В третьем и пятом преобразованиях
    использовано сделанное выше замечание, в четвертом —
    @cond:kubota-four-matrix-entries, в шестом — то же замечание, в седьмом —
    @cond:kubota-four-matrix-entries и
    @prop:mennicke-symbol-elementary-properties @cond:mennicke-unit-symbol, в
    последнем — @prop:mennicke-symbol-elementary-properties
    @cond:kervaire-symbol-transfer.
  ] <cond:kubota-comaximal-multiplicativity>

  #source(245)
  #condition-item[
    _Отображение $k$ — гомоморфизм, т.~е. $H = GL_2 (A, frak(q))$._

    Пусть $alpha$, $alpha' in GL_2 (A, frak(q))$. Покажем, что
    $k(alpha' alpha) = k(alpha') k(alpha)$. Предположим, что
    $alpha = alpha_1 alpha_2$, где $alpha_2 in GE_2 (A, frak(q)) subset H$ (см.
    @cond:kubota-elementary-invariance). Тогда
    $k(alpha' alpha) = k(alpha' alpha_1)$, в то время как, также в силу
    @cond:kubota-elementary-invariance, $k(alpha) = k(alpha_1)$. Следовательно,
    мы вольны заменять $alpha$ на $alpha alpha_2^(-1)$ для любого элемента
    $alpha_2 in GE_2 (A, frak(q))$. Сначала добьемся того, чтобы
    $det(alpha) = 1$.

    Пусть $a' = 1 + t$. Если $t = 0$, то можно применить
    @cond:kubota-comaximal-multiplicativity и закончить доказательство. В
    противном случае в силу @cor:semilocal-relative-special-linear-surjection
    можно выбрать элемент $epsilon_1 in E_2 (A, frak(q))$ так, чтобы
    $alpha epsilon_1 in SL_2 (A, t A)$, скажем
    $alpha epsilon_1 = mat(a_1, b_1; c_1, d_1)$. Так как
    $d_1 A + c_1 A = A = d_1 A + c_1^2 A$, то можно найти элемент
    $d_2 = d_1 + s c_1^2$ ($s in A$), который обратим по модулю $a'$. Положим
    $epsilon_2 = I + c_1 s e_(1 2) in E_2 (A, t A)$. Тогда
    $alpha epsilon_1 epsilon_2 = mat(a_1, b_1 + c_1 s a_1; c_1, d_2)$ и поэтому
    выполнены предположения части @cond:kubota-comaximal-multiplicativity для
    элементов $alpha epsilon_1 epsilon_2$ и $alpha'$. Следовательно, в силу
    @cond:kubota-comaximal-multiplicativity и
    @cond:kubota-elementary-invariance
    $
      k(alpha' alpha) = k(alpha' alpha epsilon_1 epsilon_2)
      = k(alpha') k(alpha epsilon_1 epsilon_2) = k(alpha') k(alpha).
    $
  ] <cond:kubota-homomorphism>

  #condition-item[
    _$Ker(k)$ содержит $GE_2 (A, frak(q))$ и $[GE_2 (A), GL_2 (A, frak(q))]$._

    Это немедленно следует из @cond:kubota-elementary-invariance.
  ] <cond:kubota-homomorphism-kernel>

  #condition-item[
    _Если матрицы $alpha$, $alpha' in GL_2 (A, frak(q))$ имеют вид
    $alpha = mat(1 + a t, b; c t, d)$ и $alpha' = mat(1 + a t, b t; c, d)$, где
    $a, t in frak(q)$, то $k(alpha) = k(alpha')$._

    Учитывая @th:mennicke-symbol-homomorphism-criterion
    @cond:mennicke-matrix-transfer-criterion, видим, что
    $
      k(alpha') = mennicke(b t, 1 + a t)
      = mennicke(b, 1 + a t) mennicke(t, 1 + a t)
      = mennicke(b, 1 + a t) = k(alpha).
    $
  ] <cond:kubota-matrix-transfer>
]

Утверждения теоремы Куботы @ss:kubota-mennicke-homomorphism содержатся в
@cond:kubota-homomorphism, @cond:kubota-homomorphism-kernel и
@cond:kubota-matrix-transfer.
