#!/usr/bin/env python3
# author: Steven Landau (skl8881@g.rit.edu)

import argparse
import sys
import time
import pprint
import random
import re
import requests
import sympy
import numpy
from collections import defaultdict
from bs4 import BeautifulSoup
from difflib import SequenceMatcher
from fractions import gcd
from sympy import Symbol


"""
TODO
-Rework the way I handle command line input
-Add functionality to balance equations (make this into a full on compiler with a parse tree?)
   -Add functionality to do redox reactions - DONE
   -Add functionality to do balancing when in an acidic/basic solution
   -Add functionality to determine the state of each of the molecules
   -Add functionality to balance charges as well. - Added charges
   -Add functionality to solve combustion reactions
   -Add functionality to solve enthalpy reactions
   -Add functionality to solve all trivial reaction formulas - DONE
   -Add functionality to find the amount_produceable reagent - DONE more or less
   -Add functionality to output the charge of an atom - DONE
   -Add functionality to output the number of valance electrons of an atom
   -Add functionality to determine the electronegativity of an atom
   -Add functionality to solve for molarity
   -Add fucntionality for quantum numbers
   -Add functionality to display electron configurations


-Add functionality to convert mass to moles - DONE
-Add functionality to tell you the mass of a molecule - DONE
-Prettify the output - DONE
-Add functionality so that you can get the symbol of an element without having its mass exactly correct - DONE
-Add functionality to get the full name of an element when given the symbol and vice versa - DONE
"""

# DO NOT TOUCH ANY OF THESE DICTIONARIES! IF YOU DON'T KNOW WHAT YOU'RE DOING YOU WILL FUCK IT UP

# Dictionary mapping a mass (string) to the name (or symbol, havent decided) of an element
mass_to_symbol = {'1.008': 'H', '4.002602': 'He', '6.94': 'Li', '9.012182': 'Be', '10.81': 'B', '12.011': 'C',
                  '14.007': 'N', '15.999': 'O', '18.9984032': 'F', '20.1797': 'Ne', '22.98976928': 'Na', '24.305': 'Mg',
                  '26.9815386': 'Al', '28.085': 'Si', '30.973762': 'P', '32.06': 'S', '35.45': 'Cl', '39.948': 'Ar',
                  '39.0983': 'K', '40.078': 'Ca', '44.955912': 'Sc', '47.867': 'Ti', '50.9415': 'V', '51.9961': 'Cr',
                  '54.938045': 'Mn', '55.845': 'Fe', '58.933195': 'Co', '58.6934': 'Ni', '63.546': 'Cu', '65.38': 'Zn',
                  '69.723': 'Ga', '72.63': 'Ge', '74.92160': 'As', '78.96': 'Se', '79.904': 'Br', '83.798': 'Kr',
                  '85.4678': 'Rb', '87.62': 'Sr', '88.90585': 'Y', '91.224': 'Zr', '92.90638': 'Nb', '95.96': 'Mo',
                  '98': 'Tc', '101.07': 'Ru', '102.90550': 'Rh', '106.42': 'Pd', '107.8682': 'Ag', '112.411': 'Cd',
                  '114.818': 'In', '118.710': 'Sn', '121.760': 'Sb', '127.60': 'Te', '126.90447': 'I', '131.293': 'Xe',
                  '132.9054519': 'Cs', '137.327': 'Ba', '178.49': 'Hf', '180.94788': 'Ta', '183.84': 'W',
                  '186.207': 'Re', '190.23': 'Os', '192.217': 'Ir', '195.084': 'Pt', '196.966569': 'Au', '200.59': 'Hg',
                  '204.38': 'Tl', '207.2': 'Pb', '208.98040': 'Bi', '209': 'Po', '210': 'At', '222': 'Rn', '223': 'Fr',
                  '226': 'Ra', '267': 'Rf', '268': 'Db', '271': 'Sg', '272': 'Bh', '270': 'Hs', '276': 'Mt',
                  '281': 'Ds', '280': 'Rg', '285': 'Cn', '284': 'Nh', '289': 'Fl', '288': 'Mc', '293': 'Lv',
                  '294': 'Ts', '138.90547': 'La', '140.116': 'Ce', '140.90765': 'Pr', '144.242': 'Nd',
                  '145': 'Pm', '150.36': 'Sm', '151.964': 'Eu', '157.25': 'Gd', '158.92535': 'Tb', '162.500': 'Dy',
                  '164.93032': 'Ho', '167.259': 'Er', '168.93421': 'Tm', '173.054': 'Yb', '174.9668': 'Lu', '227': 'Ac',
                  '232.03806': 'Th', '231.03588': 'Pa', '238.02891': 'U', '237': 'Np', '244': 'Pu', '243': 'Am',
                  '247': 'Cm', '251': 'Cf', '252': 'Es', '257': 'Fm', '258': 'Md', '259': 'No',
                  '262': 'Lr'}

# Dictionary mapping the symbol of an element to the mass of that element.
symbol_to_mass = {'H': '1.008', 'He': '4.002602', 'Li': '6.94', 'Be': '9.012182', 'B': '10.81', 'C': '12.011',
                  'N': '14.007', 'O': '15.999', 'F': '18.9984032', 'Ne': '20.1797', 'Na': '22.98976928', 'Mg': '24.305',
                  'Al': '26.9815386', 'Si': '28.085', 'P': '30.973762', 'S': '32.06', 'Cl': '35.45', 'Ar': '39.948',
                  'K': '39.0983', 'Ca': '40.078', 'Sc': '44.955912', 'Ti': '47.867', 'V': '50.9415', 'Cr': '51.9961',
                  'Mn': '54.938045', 'Fe': '55.845', 'Co': '58.933195', 'Ni': '58.6934', 'Cu': '63.546', 'Zn': '65.38',
                  'Ga': '69.723', 'Ge': '72.63', 'As': '74.92160', 'Se': '78.96', 'Br': '79.904', 'Kr': '83.798',
                  'Rb': '85.4678', 'Sr': '87.62', 'Y': '88.90585', 'Zr': '91.224', 'Nb': '92.90638', 'Mo': '95.96',
                  'Tc': '98', 'Ru': '101.07', 'Rh': '102.90550', 'Pd': '106.42', 'Ag': '107.8682', 'Cd': '112.411',
                  'In': '114.818', 'Sn': '118.710', 'Sb': '121.760', 'Te': '127.60', 'I': '126.90447', 'Xe': '131.293',
                  'Cs': '132.9054519', 'Ba': '137.327', 'Hf': '178.49', 'Ta': '180.94788', 'W': '183.84',
                  'Re': '186.207', 'Os': '190.23', 'Ir': '192.217', 'Pt': '195.084', 'Au': '196.966569', 'Hg': '200.59',
                  'Tl': '204.38', 'Pb': '207.2', 'Bi': '208.98040', 'Po': '209', 'At': '210', 'Rn': '222', 'Fr': '223',
                  'Ra': '226', 'Rf': '267', 'Db': '268', 'Sg': '271', 'Bh': '272', 'Hs': '270', 'Mt': '276',
                  'Ds': '281', 'Rg': '280', 'Cn': '285', 'Nh': '284', 'Fl': '289', 'Mc': '288', 'Lv': '293',
                  'Ts': '294', 'Og': '294', 'La': '138.90547', 'Ce': '140.116', 'Pr': '140.90765', 'Nd': '144.242',
                  'Pm': '145', 'Sm': '150.36', 'Eu': '151.964', 'Gd': '157.25', 'Tb': '158.92535', 'Dy': '162.500',
                  'Ho': '164.93032', 'Er': '167.259', 'Tm': '168.93421', 'Yb': '173.054', 'Lu': '174.9668', 'Ac': '227',
                  'Th': '232.03806', 'Pa': '231.03588', 'U': '238.02891', 'Np': '237', 'Pu': '244', 'Am': '243',
                  'Cm': '247', 'Bk': '247', 'Cf': '251', 'Es': '252', 'Fm': '257', 'Md': '258', 'No': '259',
                  'Lr': '262'}

# Dictionary mapping the symbol of an element to the atomic # of that element.
symbol_to_number = {'H': '1', 'He': '2', 'Li': '3', 'Be': '4', 'B': '5', 'C': '6', 'N': '7', 'O': '8', 'F': '9',
                    'Ne': '10', 'Na': '11', 'Mg': '12', 'Al': '13', 'Si': '14', 'P': '15', 'S': '16', 'Cl': '17',
                    'Ar': '18', 'K': '19', 'Ca': '20', 'Sc': '21', 'Ti': '22', 'V': '23', 'Cr': '24', 'Mn': '25',
                    'Fe': '26', 'Co': '27', 'Ni': '28', 'Cu': '29', 'Zn': '30', 'Ga': '31', 'Ge': '32', 'As': '33',
                    'Se': '34', 'Br': '35', 'Kr': '36', 'Rb': '37', 'Sr': '38', 'Y': '39', 'Zr': '40', 'Nb': '41',
                    'Mo': '42', 'Tc': '43', 'Ru': '44', 'Rh': '45', 'Pd': '46', 'Ag': '47', 'Cd': '48', 'In': '49',
                    'Sn': '50', 'Sb': '51', 'Te': '52', 'I': '53', 'Xe': '54', 'Cs': '55', 'Ba': '56', 'Hf': '72',
                    'Ta': '73', 'W': '74', 'Re': '75', 'Os': '76', 'Ir': '77', 'Pt': '78', 'Au': '79', 'Hg': '80',
                    'Tl': '81', 'Pb': '82', 'Bi': '83', 'Po': '84', 'At': '85', 'Rn': '86', 'Fr': '87', 'Ra': '88',
                    'Rf': '104', 'Db': '105', 'Sg': '106', 'Bh': '107', 'Hs': '108', 'Mt': '109', 'Ds': '110',
                    'Rg': '111', 'Cn': '112', 'Nh': '113', 'Fl': '114', 'Mc': '115', 'Lv': '116', 'Ts': '117',
                    'Og': '118', 'La': '57', 'Ce': '58', 'Pr': '59', 'Nd': '60', 'Pm': '61', 'Sm': '62', 'Eu': '63',
                    'Gd': '64', 'Tb': '65', 'Dy': '66', 'Ho': '67', 'Er': '68', 'Tm': '69', 'Yb': '70', 'Lu': '71',
                    'Ac': '89', 'Th': '90', 'Pa': '91', 'U': '92', 'Np': '93', 'Pu': '94', 'Am': '95', 'Cm': '96',
                    'Bk': '97', 'Cf': '98', 'Es': '99', 'Fm': '100', 'Md': '101', 'No': '102', 'Lr': '103'}

# Dictionary linking every elements symbol to its full name
symbol_to_name = {'H': 'Hydrogen', 'He': 'Helium', 'Li': 'Lithium', 'Be': 'Beryllium', 'B': 'Boron', 'C': 'Carbon',
                  'N': 'Nitrogen', 'O': 'Oxygen', 'F': 'Fluorine', 'Ne': 'Neon', 'Na': 'Sodium', 'Mg': 'Magnesium',
                  'Al': 'Aluminium', 'Si': 'Silicon', 'P': 'Phosphorus', 'S': 'Sulfur', 'Cl': 'Chlorine', 'Ar': 'Argon',
                  'K': 'Potassium', 'Ca': 'Calcium', 'Sc': 'Scandium', 'Ti': 'Titanium', 'V': 'Vanadium',
                  'Cr': 'Chromium', 'Mn': 'Manganese', 'Fe': 'Iron', 'Co': 'Cobalt', 'Ni': 'Nickel', 'Cu': 'Copper',
                  'Zn': 'Zinc', 'Ga': 'Gallium', 'Ge': 'Germanium', 'As': 'Arsenic', 'Se': 'Selenium', 'Br': 'Bromine',
                  'Kr': 'Krypton', 'Rb': 'Rubidium', 'Sr': 'Strontium', 'Y': 'Yttrium', 'Zr': 'Zirconium',
                  'Nb': 'Niobium', 'Mo': 'Molybdenum', 'Tc': 'Technetium', 'Ru': 'Ruthenium', 'Rh': 'Rhodium',
                  'Pd': 'Palladium', 'Ag': 'Silver', 'Cd': 'Cadmium', 'In': 'Indium', 'Sn': 'Tin', 'Sb': 'Antimony',
                  'Te': 'Tellurium', 'I': 'Iodine', 'Xe': 'Xenon', 'Cs': 'Caesium', 'Ba': 'Barium', 'Hf': 'Hafnium',
                  'Ta': 'Tantalum', 'W': 'Tungsten', 'Re': 'Rhenium', 'Os': 'Osmium', 'Ir': 'Iridium', 'Pt': 'Platinum',
                  'Au': 'Gold', 'Hg': 'Mercury', 'Tl': 'Thallium', 'Pb': 'Lead', 'Bi': 'Bismuth', 'Po': 'Polonium',
                  'At': 'Astatine', 'Rn': 'Radon', 'Fr': 'Francium', 'Ra': 'Radium', 'Rf': 'Rutherfordium',
                  'Db': 'Dubnium', 'Sg': 'Seaborgium', 'Bh': 'Bohrium', 'Hs': 'Hassium', 'Mt': 'Meitnerium',
                  'Ds': 'Darmstadtium', 'Rg': 'Roentgenium', 'Cn': 'Copernicium', 'Nh': 'Nihonium', 'Fl': 'Flerovium',
                  'Mc': 'Moscovium', 'Lv': 'Livermorium', 'Ts': 'Tennessine', 'Og': 'Oganesson', 'La': 'Lanthanum',
                  'Ce': 'Cerium', 'Pr': 'Praseodymium', 'Nd': 'Neodymium', 'Pm': 'Promethium', 'Sm': 'Samarium',
                  'Eu': 'Europium', 'Gd': 'Gadolinium', 'Tb': 'Terbium', 'Dy': 'Dysprosium', 'Ho': 'Holmium',
                  'Er': 'Erbium', 'Tm': 'Thulium', 'Yb': 'Ytterbium', 'Lu': 'Lutetium', 'Ac': 'Actinium',
                  'Th': 'Thorium', 'Pa': 'Protactinium', 'U': 'Uranium', 'Np': 'Neptunium', 'Pu': 'Plutonium',
                  'Am': 'Americium', 'Cm': 'Curium', 'Bk': 'Berkelium', 'Cf': 'Californium', 'Es': 'Einsteinium',
                  'Fm': 'Fermium', 'Md': 'Mendelevium', 'No': 'Nobelium', 'Lr': 'Lawrencium'}

# Dictionary linking an elements symbol to its (most common) charge
"""
symbol_to_charge = {'H': '+1', 'Li': '+1', 'Na': '+1', 'K': '+1', 'Rb': '+1', 'Cs': '+1', 'Be': '+2', 'Mg': '+2',
                    'Ca': '+2', 'Sr': '+2', 'Ba': '+2', 'B': '0', 'Al': '+3', 'C': '0', 'Si': '0', 'Sn': '+2',
                    'Pb': '+2', 'N': '-3', 'P': '-3', 'As': '0', 'O': '-2', 'S': '-2', 'F': '-1', 'Cl': '-1',
                    'Br': '-1', 'I': '-1', 'Cr': '+2', 'Mn': '+2', 'Fe': '+2', 'Co': '+2', 'Ni': '+2', 'Cu': '+2',
                    'Zn': '+2', 'Ag': '+1', 'Cd': '+2', 'Hg': '+2'}

"""

symbol_to_charge = {'Li': '+1', 'Na': '+1', 'K': '+1', 'Rb': '+1', 'Cs': '+1', 'Fr': '+1', 'Be': '+2', 'Mg': '+2',
                    'Ca': '+2', 'Sr': '+2', 'Ba': '+2', 'Ra': '+2', 'Sc': '+3', 'Y': '+3', 'La': '+3', 'Cr': '+2',
                    'Mn': '+2', 'Fe': '+2', 'Co': '+2', 'Ni': '+2', 'Cu': '+1', 'Ag': '+1', 'Au': '+1', 'Zn': '+2',
                    'Cd': '+2', 'Hg': '+1', 'Al': '+3', 'Ga': '+3', 'In': '+1', 'Tl': '+1', 'Sn': '+2', 'Pb': '+2',
                    'Bi': '+3', 'C': '-4', 'N': '-3', 'P': '-3', 'O': '-2', 'S': '-2', 'Se': '-2', 'Te': '-2',
                    'F': '-1', 'Cl': '-1', 'Br': '-1', 'I': '-1', 'H': '+1'}

polyatomic_ions_to_charge = {'NH4': '+1', 'OH': '-1', 'CN': '-1', 'SO4': '-2', 'O2': '-2', 'CNO': '-1', 'HSO4': '-1',
                             'C2H3O2': '-1', 'SCN': '-1', 'SO3': '-2', 'ClO4': '-1', 'CO3': '-2', 'NO3': '-1',
                             'ClO3': '-1', 'HCO3': '-1', 'NO2': '-1', 'ClO2': '-1', 'C2O4': '-2', 'PO4': '-3',
                             'ClO': '-1', 'S2O3': '-2', 'HPO4': '-1', 'Cr2O7': '-2', 'H3O': '+1', 'PO3': '-3',
                             'MnO4': '-1', 'NH3': '0'}


# Errors


class InvalidSymbolException(Exception):
    def __init__(self, message):
        self.message = message


class InvalidNameException(Exception):
    def __init__(self, message):
        self.message = message


class ProductsNotFoundException(Exception):
    def __init__(self, message):
        self.message = message


class InvalidEquationException(Exception):
    def __init__(self, message):
        self.message = message

# Graph stuff


class CompoundNode:
    def __init__(self, compound):
        self.unaltered_compound = compound  # The original, unaltered compound
        self.adjacent = {}  # may not even need to make this a graph
        self.moles_of_compound = 1  # Number of moles of given compound
        self.elements_dict = {}  # A dictionary linking each element in the
        # compound to their given number of moles ex: H: 3
        self.elements_queue = []  # To be used to keep track of the order of the elements
        self.mass = 0  # Mass of entire compound (moles_of_compound taken into account)
        self.charge = 0  # Charge of entire compound (moles of compound taken into account)
        self.__analyze_compound__()  # analyze the compound and establish all above variables

    def __analyze_compound__(self):
        moles_of_compound = re.match(r'(^\d*)', self.unaltered_compound)
        self.moles_of_compound = 1 if moles_of_compound.group(1) is '' else moles_of_compound.group(1)

        contents = re.findall(r"(([A-Z][a-z]?\d*)|(\(([A-Z][a-z]?\d*)*\)\d*))", self.unaltered_compound)
        for elem in contents:
            elem = elem[0]
            # TODO handle (SO4)3
            if elem.startswith('('):
                moles_of_polyatom = re.search(r"(?P<moles>\d*$)", elem)
                moles_of_polyatom = 1 if moles_of_polyatom.group('moles') is '' else float(moles_of_polyatom.group('moles'))

                polyatomic_ion = re.search(r"\((?P<poly>.*)\)", elem)
                polyatomic_ion = polyatomic_ion.group('poly')

                self.elements_dict[polyatomic_ion] = float(moles_of_polyatom)
                self.elements_queue.append(polyatomic_ion)

                mass = massOfCompound(polyatomic_ion, format_return=False)
                self.mass += float(mass) * float(self.elements_dict[polyatomic_ion])

                try:
                    charge = polyatomic_ions_to_charge[polyatomic_ion]
                    if charge[0] == '+':
                        self.charge += int(charge[1:]) * int(moles_of_polyatom)
                    if charge[0] == '-':
                        self.charge -= int(charge[1:])
                except KeyError:
                    pass

                continue

            moles_of_element = re.match(r"\D*(?P<moles>\d*)", elem)
            moles_of_element = moles_of_element.group('moles')
            #print(elem, moles_of_element)
            element = re.match(r"(?P<element>^\D*)", elem)
            element = element.group('element')

            self.elements_dict[element] = 1 if moles_of_element is '' else float(moles_of_element)
            #print(elem, self.elements_dict[element])
            self.elements_queue.append(element)
            self.mass += float(symbol_to_mass[element]) * float(self.elements_dict[element])

            try:
                charge = symbol_to_charge[element]
                if charge[0] == '+':
                    self.charge += int(charge[1:])
                if charge[0] == '-':
                    self.charge -= int(charge[1:])
                else:
                    pass  # charge is 0

            except KeyError:
                # Charge is 0. No need to add it
                pass

        self.mass *= float(self.moles_of_compound)
        self.charge *= float(self.moles_of_compound)

    def __repr__(self):
        compound_without_moles = re.match(r'^\d*(.*)', self.unaltered_compound.strip())
        compound_without_moles = compound_without_moles.group(1)
        return compound_without_moles

    def __str__(self):
        compound_without_moles = re.match(r'^\d*(.*)', self.unaltered_compound.strip())
        compound_without_moles = compound_without_moles.group(1)
        return compound_without_moles

    def __contains__(self, item):
        keys = self.elements_dict
        for elem in keys:
            if elem == item:
                return True

        return False

    def get_element_dict(self):
        temp_dict = self.elements_dict.copy()
        for entry in temp_dict:
            temp_dict[entry] = float(temp_dict[entry]) * float(self.moles_of_compound)
        return temp_dict

    def add_neighbor(self, neighbor, weight=0):
        self.adjacent[neighbor] = weight

    def get_unaltered_compound(self):
        return self.unaltered_compound

    def get_moles_of_compound(self):
        return self.moles_of_compound

    def change_moles_of_compound(self, moles):
        self.moles_of_compound = moles
        normal_charge = self.charge / (float(self.moles_of_compound))
        self.charge = normal_charge * float(moles)


# Functions


def balance(equation: str, return_moles=False):
    """
    Determine the number of moles each compound needs on both sides of the equation in order
    to have the same number of elements on both sides.
    :param equation: The string of the given equation. Ex: H2 + O2 -> H2O
    :param return_moles: If false, return moles makes the function return a string of the balanced equation. If false (default)
    the function returns a list of the balanced moles, positive numbers in the list are reactants, negative are products.
    :return: Either a string of the balanced element, or a list of the balanced moles (if return_moles is True)
    """
    # Begin by splitting the equation into two parts. Reactants and Products

    if equation.__contains__('->'):
        splitter = '->'
    elif equation.__contains__('-->'):
        splitter = '-->'
    elif equation.__contains__('='):
        splitter = '='
    else:
        raise ProductsNotFoundException('No \"->\", \"-->\" or \"=\" found.')

    expanded_equation = expand_equation(equation)

    equation_list = expanded_equation.split(splitter)
    
    reactant_side = 0
    product_side = 1

    reactants = equation_list[reactant_side].split('+')
    products = equation_list[product_side].split('+')
    reactant_nodes, product_nodes = create_nodes_from_eq(reactants, products)

    printable_equation_list = equation.split(splitter)
    for index in range(len(printable_equation_list)):
        printable_equation_list[index] = printable_equation_list[index].replace(" ", "")

    printable_reactants = printable_equation_list[reactant_side].split('+')

    printable_products = printable_equation_list[product_side].split('+')

    enforce_conservation_of_matter(reactant_nodes, product_nodes)

    equation_node_list = reactant_nodes + product_nodes
    elements_set = get_elements_set(equation_node_list)

    elements_matrix = create_matrix(elements_set, equation_node_list)

    balanced_moles_in_decimal = find_null_space(elements_matrix)

    if return_moles:
        return decimal_to_moles(balanced_moles_in_decimal)

    final_col = []
    for number in balanced_moles_in_decimal:
        final_col.append(abs(number[0]))

    # The final_col contains decimals right now. We need to divide by the smallest to determine the number of moles
    moles_list = decimal_to_moles(final_col)

    intify_moles(moles_list)

    output = ""
    for index, compound in enumerate(printable_reactants):
        output += str(moles_list[index]) + str(compound)
        if index != len(reactant_nodes) - 1:
            output += ' + '

    output += ' --> '

    for index, compound in enumerate(printable_products):
        output += str(moles_list[index + len(reactant_nodes)]) + str(compound)
        if index != len(product_nodes) - 1:
            output += ' + '

    return output


def enforce_conservation_of_matter(reactant_nodes, product_nodes):
    """
    Makes sure the given equation is valid. Mainly determines if elements given in the reactant are also in the products and vice versa.
    Raises an error if an element on one side is not found in the other.
    :param reactant_nodes: A list of the reactants in the form of CompoundNodes
    :param product_nodes: A list of products in the form of CompoundNodes
    :return: None
    """
    elements_reactant = set()
    for compound in reactant_nodes:
        for element in compound.elements_dict:
            potential_elements = re.findall(r'[A-Z][a-z]?', element)
            if len(potential_elements) > 1:
                for elem in potential_elements:
                    elements_reactant.add(elem)
            else:
                elements_reactant.add(element)

    elements_products = set()
    for compound in product_nodes:
        for element in compound.elements_dict:
            potential_elements = re.findall(r'[A-Z][a-z]?', element)
            if len(potential_elements) > 1:
                for elem in potential_elements:
                    elements_products.add(elem)
            else:
                elements_products.add(element)

    for element in elements_reactant:
        potential_elements = re.findall(r'[A-Z][a-z]?', element)
        num_of_elements = len(potential_elements)

        if num_of_elements > 1:
            polyatom = element
            for elem in polyatom: # TODO There is probably a better, more reliable way to handle this
                if elem not in elements_products:
                    raise InvalidSymbolException('{element} not found in products'.format(element=element))
        elif element not in elements_products:
            raise InvalidEquationException('{element} not found in Products'.format(element=element))

    for element in elements_products:
        potential_elements = re.findall(r'[A-Z][a-z]?\d*', element)
        num_of_elements = len(potential_elements)

        if num_of_elements > 1:
            polyatom = element
            for elem in polyatom:  # TODO There is probably a better, more reliable way to handle this
                if elem not in elements_reactant:
                    raise InvalidSymbolException('{element} not found in products'.format(element=element))

        elif element not in elements_reactant:
            raise InvalidEquationException('{element} not found in Reactants'.format(element=element))


def expand_equation(equation):
    """
    Takes all polyatomic ions on the equation and expands them. Ex: (SO3)4 -> S4O12
    :param equation: The unmodified string of the given equation
    :return: The expanded string of the equation
    """
    polyatomic_ions = re.findall(r'(\(([A-Z][a-z]?\d*)+\)\d*)', str(equation))

    entire_atom_index = 0
    for polyatom in polyatomic_ions:
        polyatom = polyatom[entire_atom_index]

        moles_of_polyatom = re.search(r'[A-Z][a-z]?\d*[A-Z]?[a-z]?\d*\)(\d*)', polyatom)
        moles_of_polyatom = 1 if moles_of_polyatom.group(1) == '' else int(moles_of_polyatom.group(1))

        elements_in_polyatom = re.findall(r'([A-Z][a-z]?\d*)', polyatom)
        new_polyatom = ""
        for element in elements_in_polyatom:
            symbol = re.match('([A-Z][a-z]?)', element)
            symbol = symbol.group(1)

            moles_of_element = re.search(r'\D*(\d*)', element)
            moles_of_element = 1 if moles_of_element.group(1) == '' else int(moles_of_element.group(1))

            moles_of_element *= moles_of_polyatom
            new_polyatom += symbol + str(moles_of_element)

        equation = equation.replace(polyatom, new_polyatom)

    return equation


def get_elements_set(equation_node_list):
    """
    Search the the equation_list which consists of CompoundNodes and obtain a set of the elements in the equation
    :param equation_node_list: A list which consists of CompoundNodes created from the original equation
    :return: A list of each element in the equation (non repeating)
    """
    elements_set = []
    for compound in equation_node_list:
        for element in compound.elements_dict:
            if element not in elements_set:
                elements_set.append(element)

    return elements_set


def create_matrix(elements_set: list, equation: list):
    """
    Creates a two dimensional matrix out of the element elements set and equation (list).
    Each row represents a different element. Each column represents a compound.
    Ex: H2 + O2 -> H2O
        H2  O2  H2O
    H   2   0   2
    O   0   2   1

    :param elements_set: A list of individual elements in the equation (non repeating)
    :param equation: A list of all compounds (in the form of ComopundNodes) in the equation.
    :return: A two dimensional array of all elements to compounds in the equation.
    """
    elements_matrix = []
    for unique_element in elements_set:
        row = []
        for compound in equation:

            found = False
            for piece in compound.elements_dict:
                if piece == unique_element:
                    found = True
                    row.append(compound.elements_dict[piece])
                    break

            if not found:
                row.append(0)

        elements_matrix.append(row)

    return elements_matrix


def find_null_space(twoD_array):
    """
    Determines the null space of a given matrix
    :param twoD_array: A two dimensional array made from the create_matrix function.
    :return: A list of floats (the null space). Negative values are products, positive are reactants.
    The list contains decimals and should be converted to moles. Each value corresponds to a
    compound in the given equation.
    """
    element_mat = numpy.atleast_2d(twoD_array)
    u, s, vh = numpy.linalg.svd(element_mat)
    default_return = 1e-13
    tol = max(default_return, 0 * s[0])
    nnz = (s >= tol).sum()
    ns = vh[nnz:].conj().T
    return ns


def decimal_to_moles(decimals: list):
    """
    Determines hte minimum value in the list and divides every value by the minimum
    :param decimals: A list of float values
    :return: A list containing moles of each element in the equation.
    Each mole corresponds to a compound in the equation (left to right).
    """
    minimum = min(decimals)
    for index in range(len(decimals)):
        decimals[index] = decimals[index] / minimum
    return decimals


def validate_balancing(reactant_nodes, product_nodes):
    """
    Ensures that the equation is properly balanced.
    :param reactant_nodes: A list of the reactant nodes (CompoundNodes) in the equation.
    :param product_nodes: A list of the reactant nodes (CompoundNodes) in the equation.
    :return: Returns True if the number of moles of each element is the same on both sides. False otherwise.
    """
    elements_tally_react = {}
    for compound in reactant_nodes:
        for element in compound.elements_dict:
            if element in elements_tally_react:
                elements_tally_react[element] += compound.elements_dict[element]
            else:
                elements_tally_react[element] = compound.elements_dict[element]

    elements_tally_prod = {}
    for compound in product_nodes:
        for element in compound.elements_dict:
            if element in elements_tally_prod:
                elements_tally_prod[element] += compound.elements_dict[element]
            else:
                elements_tally_prod[element] = compound.elements_dict[element]

    for element, moles in elements_tally_react.items():
        if moles != elements_tally_prod[element]:
            return False

    return True


def create_nodes_from_eq(reactants: list, products: list):
    """
    Creates CompoundNodes from the reactants and products lists
    :param reactants: A list of the reactants
    :param products: A list of the products
    :return: A list of the reactant_nodes and product_nodes, each of which contain CompoundNodes
    """
    reactant_nodes = []
    product_nodes = []
    for ingredient in reactants:
        if ingredient == '+' or ingredient == '(s)' or ingredient == '(l)' \
                or ingredient == '(g)' or ingredient == '(aq)':
            continue
        reactant_nodes.append(CompoundNode(ingredient))

    for result in products:
        if result == '+' or result == '(s)' or result == '(l)' or result == '(g)' or result == '(aq)':
            continue
        product_nodes.append(CompoundNode(result))

    return reactant_nodes, product_nodes


def intify_moles(moles: list):
    """
    Turns half moles into whole moles. Modifies the list (in place), 
    doubling each value if a value of 1.5 moles is detected.
    :param moles: A list of moles in the equation.
    :return: None
    """
    for number in moles:
        if number == 1.5:
            fraction = number.as_integer_ratio()
            for index in range(len(moles)):
                moles[index] = moles[index] * fraction[1]



def get_mass(symbol: str, format_return=True):
   """
   Determines and returns the mass of an individual symbol.
   :param symbol: An individual element on the periodic table.
   :param format_return: True if the return is to be formatted and ready for immediate output. False if the mass alone is to be returned.
   :return: The mass of the individual element (formatted or not depending on format_return).
   """
    sanitized_symbol = sanitize_element(symbol)
    if format_return:
        ret_val = "The mass of " + symbol_to_name[sanitized_symbol] + ' (' + sanitized_symbol \
                  + ") is " + symbol_to_mass[sanitized_symbol] + "g/mol"
    else:
        ret_val = symbol_to_mass[sanitized_symbol]
    return ret_val


def sanitize_element(symbol: str):
   """
   Puts the given symbol in the correct format. Ex: na -> Na, h -> H, he -> He.
   :param symbol: The individual element on the periodic table (already formatted properly or not).
   :return: The same element but with proper formatting.
   """
    if len(symbol) == 2:
        sanitized_symbol = symbol[0].upper()  # Making sure this is in the right format
        sanitized_symbol += symbol[1].lower()
    else:
        sanitized_symbol = symbol.upper()

    return sanitized_symbol


def get_symbol(mass: str):
    """
   Obtains the elemental symbol whole mass is closest to that of the mass specified.
   :param mass: The (string) of the given mass.
   :return: The element whose mass is closest to that which was given.
   """
    match_num, closest_match = 500.0, None
    mass = float(mass)
    for entry in mass_to_symbol:
        comp = abs(float(entry) - mass)
        if comp <= match_num:
            match_num = comp
            closest_match = entry

    return mass_to_symbol[closest_match]


def get_full_name(symbol: str):
    """
   Given an elemental symbol, returns the full name of the given element.
   :param symbol: The symbol of the element one wishes to determine the full name of.
   :return: The full name of the given element
   """
    sanitized_symbol = sanitize_element(symbol)
    ret_val = sanitized_symbol + " is " + symbol_to_name[sanitized_symbol]
    return ret_val


def get_atomic_number(symbol: str, format_return=True):
    """
   Finds and returns the atomic number of the given element.
   :param symbol: The element in which the atomic number is to be retrieved.
   :param format_return: True (Default) if one wishes the return to be formatted (pretty printable) and
   false if the atomic number alone is desired.
   :return: The atomic number of the given symbol (formatted or not depending on format_return which defaults to True)
   """
    symbol = sanitize_element(symbol)
    atomic_number = symbol_to_number[symbol]
    if format_return:
        ret_val = 'The atomic number of {element} ({elem_symbol}) is {number}'.format(
            element=symbol_to_name[symbol], elem_symbol=symbol, number=atomic_number)
    else:
        ret_val = atomic_number

    return ret_val


def get_element_info(input: str, format_return=True):
    """
   Get all available information about the input (element)
   :param input: Either the name of an element or the symbol of an element
   :return: A formatted string containing all available info on the given input. If format_return is false,
   a dictionary is returned containing all relevent information.
   """
    if len(input) != 1 and len(input) != 2:  # Given the full element name
        closest_ratio = 0
        elem_name = ''

        for entry in symbol_to_name:
            val = symbol_to_name[entry]
            ratio = SequenceMatcher(a=val,
                                    b=input).ratio()  # Sequence matcher seems a bit random at times. I want to replace it in the future
            if ratio > closest_ratio:
                closest_ratio = ratio
                elem = entry
                elem_name = val

    else:  # Given the element symbol
        elem = sanitize_element(input)
        elem_name = symbol_to_name[elem]

    if format_return:
        ret_val = '{elem_name} ({elem}) has a mass of {symbol_mass}g/mol, a charge of {charge}, and an atomic number of {anum}'.format(
            elem_name=elem_name, elem=elem, symbol_mass=symbol_to_mass[elem], charge=getCharge(elem),
            anum=symbol_to_number[elem])
    else:
        ret_val = {'name': elem_name, 'element': elem, 'mass': symbol_to_mass[elem], 'charge': getCharge(elem)}

    return ret_val


def massOfCompound(compound: str, format_return=True):
    """
   :pre The compounds format must be correct. Ex: Mn will work, mn will throw an error. H will work, h will throw an error.
   :param compound: The compound whose mass is to be determined
   :return: If format_return is off, the function will return the pure mass of the compound. If format_return is on,
   the function will return the mass of the compound in printable format.
   """
    #  Cannot sanitize the string here. No way to tell if say ncsu is supposed to be Nitrigen Ceasium (Cs) and Uranium
    # or Nitrogen Carbon Sulfur and Uranium

    front_num = re.match(r"(\d*).*", compound)  # See if we are going to have to multiply the entire mass at all

    # Keep an eye on this. Not sure if I'm using .match correctly
    end_mult = 1.0 if front_num.group(1) is '' else float(front_num.group(1))

    # Find the individual elements in the compound. Will have to be parsed individually
    # later to determine how much we need to multiply the mass by.
    elements = re.findall(r"(([A-Z][a-z]?\d*)|(\([A-Z]*[a-z]?\d*\)\d*))", compound)
    mass = 0
    for elem in elements:
        elem = elem[0]  # Get the first element in the tuple
        if elem.startswith("("):
            # Ex: (SO4)3
            ending_mult = re.match(r"\(.*\)(\d*)", elem)
            ending_mult = ending_mult.group(1)
            mult = 1.0 if ending_mult is '' else float(ending_mult)

            inner_compound = re.match(r"\((.*)\)", elem)
            inner_compound = inner_compound.group(1)

            mass += float(massOfCompound(inner_compound, format_return=False)) * float(mult)

        else:
            # Ex: H3
            single_element = re.match(r"([A-Z][a-z]?)", elem)
            single_element = single_element.group(1)

            num_of_atoms = re.match(r"\D*(\d*)", elem)
            num_of_atoms = num_of_atoms.group(1)

            mult = 1.0 if num_of_atoms is '' else float(num_of_atoms)
            mass += (float(symbol_to_mass[single_element]) * mult)

    mass *= end_mult
    if format_return:
        ret_val = 'The mass of ' + compound + ' is ' + str(mass) + 'g/mol'
    else:
        ret_val = str(mass)
    return ret_val


def getCharge(symbol: str, format_return=True):
    """
    Retrieves the charge of the given element.
    :param symbol: The given element of which the charge is to be found.
    :param format_return: If format_return is True, the function will return the charge of the element in a printable format.
    Otherwise the function will return the plain charge (with the +-)
    :return: The charge of the element in printable or spartan form (depending on format return)
    """
    try:
        return symbol_to_charge[symbol]
    except KeyError:
        return '0'


def mass_to_moles(mass: str, input: str, format_return=True):
    """
    Converts the mass of the given element to moles of the given element. ex: 10gH * 1molH/1.008gH = ...
    :param mass: The mass of the given element or compound
    :param input: The element or compound in which the mass will be converted to moles for.
    :param format_return: If True, the code will be returned in a printable format. If False, the plain moles will be returned.
    :return:
    """
    result = float(mass) * (float(massOfCompound(input, format_return=False)) ** -1)
    if format_return:
        ret_val = '{grams}g of {elem} was converted to {moles} moles of {elem}'.format(grams=mass, elem=input, moles=result)
    else:
        ret_val = result

    return ret_val


def deconstruct(compound: str):
    """
    Deconstructs a given compound and returns a list of the individual elements (along with the number of moles for each in the compound)
    If the compound contains elements inside a parenthesis the output will be as follows.
    Ex: (SO3)4 -> [ ..., S, O3, 4, ... ]
    :param compound: The compound to be deconstructed
    :return: A list of all elements inside the compound (including the number of moles of that element)
    """
    front_num = re.match(r"(\d*).*", compound)
    contents = re.findall(r"(([A-Z][a-z]?\d*)|(\([A-Z]*[a-z]?\d*\)\d*))",
                          compound)  # for second part may need to do * instead of ?

    separated = []
    if front_num.group(1) is not '':
        contents.append(front_num.group(1))

    for elem in contents:
        elem = elem[0]
        if elem[0] == '(':
            inside = deconstruct(elem)
            for piece in inside:
                separated.append(piece)
        else:
            separated.append(elem)

    return separated


def amount_producible(grams_given: str, element_given: str, compound_desired: str, format_return=True):
    grams_to_moles = mass_to_moles(grams_given, element_given, format_return=False)  # Moles of element_given

    pure_element = re.match(r"(\D*)", element_given)
    pure_element = pure_element.group(1)
    moles_of_element_given = re.match(r"\D*(\d*)", element_given)

    moles_of_element_given = 1 if moles_of_element_given.group(1) is '' else moles_of_element_given.group(1)

    contents = deconstruct(compound_desired)  # Elements (with moles) of compound_desired
    for elem in contents:
        element = re.match(r"(\D*)", elem)
        moles_of_element = re.match(r"\D*(\d*)", elem)  # The element given inside the compound_desired

        moles_of_element = 1.0 if moles_of_element.group(1) is '' else moles_of_element.group(1)
        element = element.group(1)

        if element == pure_element:
            moles_of_top = 1 * float(moles_of_element_given)

            moles_of_bot = float(moles_of_element_given) * float(moles_of_element)

            to_mult = moles_of_top / moles_of_bot * float(
                moles_of_element_given)  # TODO figure out why I have to multiply by elmenet_given again

            produced = to_mult * float(grams_to_moles)
            if format_return:
                ret_val = '{grams}g of {given} would produce {moles} moles of {wanted}'.format(grams=grams_given, given=element_given, moles=produced, wanted=compound_desired)
            else:
                ret_val = produced

            return ret_val

            # Now find out how many moles of the element given are in the compound desired.

def update():
    response = requests.get('http://www.ptable.com/')
    page = BeautifulSoup(response.content, 'html.parser')

    elements = re.finditer(
        r"<strong an=\"\d+\">(?P<number>\d+)</strong> ?<acronym.*>(?P<symbol>.+)</acronym> ?<em.*?>(?P<name>.+)</em> ?<i>\(?(?P<mass>\d+\.?\d+?)\)?</i>",
        str(page))
    num_obtained = 0

    """
   Group 1: Atomic #
   Group 2: Atomic Symbol
   Group 3: Element Name
   Group 4: Atomic Mass
   """
    retrieved_mass_to_symbol = []
    retrieved_symbol_to_mass = []
    retrieved_symbol_to_number = []
    retrieved_symbol_to_name = []
    for i, element in enumerate(elements):
        num_obtained += 1
        retrieved_mass_to_symbol.append(element.group('mass'))
        retrieved_mass_to_symbol.append(element.group('symbol'))

        retrieved_symbol_to_mass.append(element.group('symbol'))
        retrieved_symbol_to_mass.append(element.group('mass'))

        retrieved_symbol_to_number.append(element.group('symbol'))
        retrieved_symbol_to_number.append(element.group('number'))

        retrieved_symbol_to_name.append(element.group('symbol'))
        retrieved_symbol_to_name.append(element.group('name'))

    # Load the file we are about to change into memory
    buf = []
    file = open('chem', 'r')
    num_lines = 0
    for i in file:
        num_lines += 1
        buf.append(i)
    file.close()

    # Determine the location of each of the dictionaries (so we can override them)
    index_mass_to_symbol = 0
    for line in buf:
        index_mass_to_symbol += 1
        if line.startswith('mass_to_symbol'):
            break

    index_mass_to_symbol -= 1  # i dont know why but we need to subtract 1

    index_symbol_to_mass = 0
    for line in buf:
        index_symbol_to_mass += 1
        if line.startswith('symbol_to_mass'):
            break

    index_symbol_to_mass -= 1

    index_symbol_to_number = 0
    for line in buf:
        index_symbol_to_number += 1
        if line.startswith('symbol_to_number'):
            break

    index_symbol_to_number -= 1

    index_symbol_to_name = 0
    for line in buf:
        index_symbol_to_name += 1
        if line.startswith('symbol_to_name'):
            break

    index_symbol_to_name -= 1

    index_symbol_to_charge = 0
    for line in buf:
        index_symbol_to_charge += 1
        if line.startswith('symbol_to_charge'):
            break
    index_symbol_to_charge -= 1

    # Build the updated dictionary which will be written to the file
    building_mass_to_symbol = "mass_to_symbol = {"
    building_symbol_to_mass = "symbol_to_mass = {"
    building_symbol_to_number = "symbol_to_number = {"
    building_symbol_to_name = "symbol_to_name = {"

    # It does not matter what we take the length of. All retrieved lists are the same length
    for mass_and_sym in range(0, len(retrieved_mass_to_symbol), 2):
        building_mass_to_symbol += ' \'' + retrieved_mass_to_symbol[mass_and_sym] + '\'' + ': ' + '\'' + \
                                   retrieved_mass_to_symbol[mass_and_sym + 1] + '\','
        building_symbol_to_mass += ' \'' + str(retrieved_symbol_to_mass[mass_and_sym]) + '\'' + ': ' + '\'' + str(
            retrieved_symbol_to_mass[mass_and_sym + 1]) + '\','
        building_symbol_to_number += ' \'' + str(retrieved_symbol_to_number[mass_and_sym]) + '\'' + ': ' + '\'' + str(
            retrieved_symbol_to_number[mass_and_sym + 1]) + '\','
        building_symbol_to_name += ' \'' + str(retrieved_symbol_to_name[mass_and_sym]) + '\'' + ': ' + '\'' + str(
            retrieved_symbol_to_name[mass_and_sym + 1]) + '\','

    building_mass_to_symbol = building_mass_to_symbol[:len(building_mass_to_symbol) - 1]
    building_mass_to_symbol += ' }\n'  # removed the last comma
    buf[index_mass_to_symbol] = building_mass_to_symbol

    building_symbol_to_mass = building_symbol_to_mass[:len(building_symbol_to_mass) - 1]
    building_symbol_to_mass += ' }\n'
    buf[index_symbol_to_mass] = building_symbol_to_mass

    building_symbol_to_number = building_symbol_to_number[:len(building_symbol_to_number) - 1]
    building_symbol_to_number += ' }\n'
    buf[index_symbol_to_number] = building_symbol_to_number

    building_symbol_to_name = building_symbol_to_name[:len(building_symbol_to_name) - 1]
    building_symbol_to_name += ' }\n'
    buf[index_symbol_to_name] = building_symbol_to_name

    # Parse another site for the charges
    # response = requests.get('http://www.chem.umass.edu/~rday/chem110/Elem00.html')
    # data = BeautifulSoup(response.content, 'html.parser')

    # symbols_and_charges = re.findall(r'')

    # write everything to the file
    file = open('chem', 'w')
    for i in range(0, num_lines):
        file.writelines(buf[i])
    file.flush()
    file.close()


def help(output=sys.stderr):
    print("elemental [command] [associated input]\n"
          "Command      Info\n"
          "mass         Prints mass of a given element. Usage: elemental mass [Element Symbol]\n\n"
          "name         Prints the name of a given elemental symbol. Usage: elemental name [Element Symbol]\n\n"
          "symbol       Prints the symbol given the name of an element. Usage: elemental symbol [Element name]\n\n"
          "compound     Prints the total mass in g/mol of a compound. Usage: elemental compound [Compound]\n\n"
          "info         Prints all available information about a given element. Usage: elemental info [Elemental symbol]\n\n"
          "anum         Prints the atomic number of a given element. Usage: elemental anum [Element Symbol]\n\n"
          "moles        Prints the moles of a given element. Usage: elemental moles [grams of element] [Elemental Symbol]\n\n"
          "limiting     Prints the number of moles that can be achieved with X grams of the given compound. Usage: elemental limiting [grams of compound or element] [element] [product]. This currently only works with an element and where there is only one product.\n\n"
          "eq           Prints the balanced version of the equation. Usage: elemental eq \"[Equation]\"\n\n", file=output)


if __name__ == '__main__':
    # a = requests.get('http://chemistry.about.com/od/chemicalbonding/fl/Element-Charges-Chart.htm')
    # b = BeautifulSoup(a.content)
    # print(b)
    # update()
    #start = time.process_time()
    result = None
    if len(sys.argv) == 1:
      help()
      exit(1)

    expected_return = sys.argv[1]  # what the user wants back.
    #parser = argparse.ArgumentParser()
    # Ex: mN would mean the user wants us to give them the mass of Nitrogen
    if expected_return == 'mass':  # The user wants the mass and gave the symbol of the element
        result = get_mass(sys.argv[2])
    elif expected_return == 'name':
        result = get_full_name(sys.argv[2])
    elif expected_return == 'symbol':  # Assume the user wants the name and gave the mass
        result = get_symbol(sys.argv[2])
    elif expected_return == 'compound':
        result = massOfCompound(sys.argv[2])
    elif expected_return == 'info':
        result = get_element_info(sys.argv[2])
    elif expected_return == 'anum':
        result = get_atomic_number(sys.argv[2])
    elif expected_return == 'moles':
        result = mass_to_moles(sys.argv[2], sys.argv[3])
    elif expected_return == 'limiting':
        result = amount_producible(sys.argv[2], sys.argv[3], sys.argv[4])
    elif expected_return == 'eq' or expected_return == 'equation':
        result = balance(sys.argv[2])
        # result = test(sys.argv[1])
    else:
        help()
        exit(0)
    print(result)
    #print('end time', time.process_time() - start)
