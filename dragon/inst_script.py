
num_dragons = int(input("Enter number of dragons: "))

output = ""

output += "inst PossibleWorldsInst {\n"
output += "    Dragon = " + " + ".join(list(map(lambda n: f"Dragon{n}", range(num_dragons)))) + "\n"
output += "    \n"
output += "    World = " + " + ".join(list(map(lambda n: f"World{n}", range(2**num_dragons - 1)))) + "\n"
output += "    eyeColors = (\n"

worlds = []
for world in range(2**num_dragons - 1):
    colors = bin(world + 2**num_dragons)[3:]
    colors = ["Green0" if x == "0" else "Blue0" for x in colors]

    assignments = []
    for dragon, color in zip(range(num_dragons), colors):
        assignments.append(f"Dragon{dragon}->{color}")

    world_text = f"        World{world}->({' + '.join(assignments)})"
    worlds.append(world_text)
output += " +\n".join(worlds) + ")\n"

output += "\n"
output += f"    #State = {num_dragons}\n"
output += f"    #Event = {num_dragons - 1}\n"
output += "}\n"

with open("instFile", "w") as f:
    f.write(output)
