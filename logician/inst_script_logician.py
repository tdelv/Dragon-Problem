
num_logicians = int(input("Enter number of logicians: "))

output = ""

output += "inst PossibleWorldsInst {\n"
output += "    Logician = " + " + ".join(list(map(lambda n: f"Logician{n}", range(num_logicians)))) + "\n"
output += "    \n"
output += "    World = " + " + ".join(list(map(lambda n: f"World{n}", range(2**num_logicians)))) + "\n"
output += "    preferences = (\n"

worlds = []
for world in range(2**num_logicians):
    preferences = bin(world + 2**num_logicians)[3:]
    preferences = ["True0" if x == "0" else "False0" for x in preferences]

    assignments = []
    for logician, preference in zip(range(num_logicians), preferences):
        assignments.append(f"Logician{logician}->{preference}")

    world_text = f"        World{world}->({' + '.join(assignments)})"
    worlds.append(world_text)
output += " +\n".join(worlds) + ")\n"

output += "\n"
output += f"    #State = {num_logicians}\n"
output += f"    #Event = {num_logicians - 1}\n"
output += "}\n"

with open("instFileLogician", "w") as f:
    f.write(output)
