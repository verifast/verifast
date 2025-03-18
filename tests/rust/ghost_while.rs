/*@

pred nonneg(n: i32) = if n == 0 { true } else { nonneg(n - 1) };

lem mk_nonneg(n: i32)
    req 0 <= n;
    ens nonneg(n);
{
    close nonneg(0);
    let i = 0;
    while i < n
        inv 0 <= i &*& i <= n &*& nonneg(i);
        decreases n - i;
    {
        i = i + 1;
        close nonneg(i);
    }
}

@*/
