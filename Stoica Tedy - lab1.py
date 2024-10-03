def suma(n: int):
    if type(n) is not int:
        return None
    suma = 0
    i = 0
    while i <= n:
        suma += i
        i += 1
    return suma

assert suma(10) == 55
assert suma(100) == 5050
assert suma(-1) == 0
assert suma(0) == 0
assert suma("asd") == None

for i in range(100):
    assert suma(i) == i*(i+1)//2

print("All tests passed")

# Use your own experience to justify that your code is correct. Write down this justification in the form of comments in your code. Try to be as detailed as possible.
"""
As the first proof, I have tested the function with different values of n, including negative values, 0 and strings. The function returns the correct value for all the cases. I have also tested that the function does not return an error when the input is not an integer, or is negative.

I have also tested the function with a range of values, and it returns the correct value for all of them. This is because the function is equivalent to the sum of the first n natural numbers, which is n*(n+1)/2. This is the formula that I have used to test the function, and it returns the correct value for all the cases.

Also, as a second proof, it should be possible to prove using induction that at each step of the loop, the value of suma is equal to the sum of the first i natural numbers, by comparing it to the formula n*(n+1)/2. This would prove that the function works for all integers. Such a proof would work like this:

- At the beginning of the loop, i = 0, and suma = 0. This is the sum of the first 0 natural numbers, which is 0.
- At each step of the loop, we add i to suma, which is the sum of the first i natural numbers. Knowking that the sum of the first i-1 natural integers is (i-1)*i/2 (by induction), we can prove that the sum of the first i natural integers is i*(i+1)/2.
- At the end of the loop, i = n, and suma = n*(n+1)/2, which is the sum of the first n natural numbers.

The first induction steps are easy to prove, as the function returns 0 for the sum of the first 0 integers, and 1 for the sum of the first 1 integer. The rest of the steps can be proven by induction, as we have shown above.
"""

# What part of your code is the most difficult to justify?
"""
The most difficult part to justify the first proof is the fact that this function works for all integers, as right now I have only tested it with a few values. 

The send proof that I have shown above should be enough to prove that the function works for all natural integers.
"""

# On a scale from 1 (the least) to 10 (the most), how convincing do you think your justification is?
"""
For the first proof this should be a 5, as it is not very convincing, since we didn't prove anything here.

The second proof should be an 8, as it is very convincing, but it is not a formal proof, as we have not shown the induction steps.
"""

# On a scale from 1 (the least) to 10 (the most), how correct do you think your justification is?
"""
For the first proof, about a 7, as at least we can be sure that the function works as expected for the values we have tested.

For the second proof, about a 9, as it is very convincing, but we have not shown the induction steps, so it is not a formal proof.
"""

# What do you think the weakest points are in your justification?

"""
For the first proof, since I did not prove that the function works for all integers, the weakest point is that there exists a function that might work for all of these tests, but will break for any other integer. For example, this function will work between 0 and 100, but will break for any other integer.

def suma(n: int):
    if n < 100:
        return n*(n+1)//2
    return None

For the second proof, the weakest point is that we have not shown the induction steps, so it is not a formal proof.
"""

# On a scale from 1 (the least) to 10 (the most), how difficult do you think it is to justify the correctness of a sorting algorithm? What are the major challenges in that case?

"""
I think it is very difficult, since we would need a way to prove mathematically that such an algorithm does not have any edge cases, such as duplicate values, or modified values. It will also be very difficult to prove that the array is actually sorted for any combination of values. So, I would rate it as a 9.
"""