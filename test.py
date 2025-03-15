def chiaya():
    n = 0
    while n < 10:
        n += 1
        yield n

kirine = chiaya()
print(kirine)