int mul(int a, int b) {
    int sum = 0;
    while (b > 0) {
        sum = sum + a;
        b = b - 1;

    };
    return sum;
}
int main() {
    int a = 10;
    int b = 20;
    b = b + 20;
    int z = mul(a, a);
    int c = mul(a, b);
    int d;
    if (a == b) {
        d = 10;
    } else {
        d = 20;
    };
    int e = c + d;
    z;
    return 0;
}
