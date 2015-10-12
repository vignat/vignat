
unsigned int guess_sqrt(unsigned int n, unsigned int guess)
{
    if (n == 0) return 0;
    if (guess == 0) return 0;
    
    if (guess*guess <= n) return guess;
    /*else*/ return guess_sqrt(n, guess - 1);
}

unsigned int sqrt(unsigned int n)
{
    return guess_sqrt(n, n);
}
